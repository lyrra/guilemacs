;;; test-font-lock-faces.el --- Test text properties with font-lock faces

(load-file "test/text-property/test-framework.el")

(test-begin "font-lock-faces")

;; Test manual application of all font-lock face types
(with-temp-buffer
  (insert "(defun my-test (arg) \"doc\" 42)")

  ;; Apply faces manually
  (put-text-property 2 7 'face 'font-lock-keyword-face)        ;; defun
  (put-text-property 8 15 'face 'font-lock-function-name-face) ;; my-test
  (put-text-property 17 20 'face 'font-lock-variable-name-face) ;; arg
  (put-text-property 22 27 'face 'font-lock-string-face)       ;; "doc"
  (put-text-property 28 30 'face 'font-lock-constant-face)     ;; 42

  ;; Verify each face was applied
  (test-eq "font-lock-faces/keyword-face"
           'font-lock-keyword-face
           (get-text-property 2 'face))

  (test-eq "font-lock-faces/function-name-face"
           'font-lock-function-name-face
           (get-text-property 8 'face))

  (test-eq "font-lock-faces/variable-name-face"
           'font-lock-variable-name-face
           (get-text-property 17 'face))

  (test-eq "font-lock-faces/string-face"
           'font-lock-string-face
           (get-text-property 22 'face))

  (test-eq "font-lock-faces/constant-face"
           'font-lock-constant-face
           (get-text-property 28 'face))

  ;; Test searching for each face type
  (test-equal "font-lock-faces/find-keyword"
              2
              (text-property-any 1 (point-max) 'face 'font-lock-keyword-face (current-buffer)))

  (test-equal "font-lock-faces/find-function-name"
              8
              (text-property-any 1 (point-max) 'face 'font-lock-function-name-face (current-buffer)))

  (test-equal "font-lock-faces/find-variable-name"
              17
              (text-property-any 1 (point-max) 'face 'font-lock-variable-name-face (current-buffer)))

  (test-equal "font-lock-faces/find-string"
              22
              (text-property-any 1 (point-max) 'face 'font-lock-string-face (current-buffer)))

  (test-equal "font-lock-faces/find-constant"
              28
              (text-property-any 1 (point-max) 'face 'font-lock-constant-face (current-buffer))))

;; Test face property operations
(with-temp-buffer
  (insert "test text")
  (put-text-property 1 5 'face 'bold)

  (test-eq "font-lock-faces/simple-bold" 'bold (get-text-property 2 'face))

  ;; Replace face
  (set-text-properties 1 5 '(face italic))
  (test-eq "font-lock-faces/replace-face" 'italic (get-text-property 2 'face))

  ;; Remove face
  (remove-text-properties 1 5 '(face))
  (test-nil "font-lock-faces/remove-face" (get-text-property 2 'face)))

(test-end)
