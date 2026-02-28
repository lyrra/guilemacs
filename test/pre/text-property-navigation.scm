;; Test cases for text property navigation functions
;; Tests for next-single-property-change, previous-single-property-change, etc.
;; Using princ with buffer as stream to insert text (insert depends on elisp code)

(deftest nspc-no-properties (nil)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (insert "hello world")
    (let ((result (next-single-property-change 1 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test with single interval - should return end of interval
(deftest nspc-single-interval (6)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (insert "hello world")
    (put-text-property 1 6 'face 'bold)
    (let ((result (next-single-property-change 1 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test from middle of interval
(deftestf 'nspc-middle-of-interval (6)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (insert "hello world")
    (put-text-property 1 6 'face 'bold)
    (let ((result (next-single-property-change 3 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test with two contiguous intervals with SAME value
;; This is the bug case - should skip to end of both intervals
(deftestf 'nspc-contiguous-same-value (9)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 5 'face 'bold)
    (put-text-property 5 9 'face 'bold)
    (let ((result (next-single-property-change 1 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test with two contiguous intervals with DIFFERENT values
(deftestf 'nspc-contiguous-different-value (5)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 5 'face 'bold)
    (put-text-property 5 9 'face 'italic)
    (let ((result (next-single-property-change 1 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test with gap between intervals
(deftestf 'nspc-with-gap (4)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 4 'face 'bold)
    (put-text-property 7 10 'face 'italic)
    (let ((result (next-single-property-change 1 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test from position before any properties
(deftestf 'nspc-before-properties (5)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 5 8 'face 'bold)
    (let ((result (next-single-property-change 1 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test with limit - should not go past limit
(deftestf 'nspc-with-limit (4)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 8 'face 'bold)
    (let ((result (next-single-property-change 1 'face nil 4)))
      (kill-buffer " ")
      (print result)))))

;; Test with multiple properties - only check one
(deftestf 'nspc-multiple-properties (5)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 5 'face 'bold)
    (put-text-property 1 8 'font-lock-face 'keyword)
    (let ((result (next-single-property-change 1 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test with three contiguous intervals with same value
(deftestf 'nspc-three-contiguous-same (10)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 4 'face 'bold)
    (put-text-property 4 7 'face 'bold)
    (put-text-property 7 10 'face 'bold)
    (let ((result (next-single-property-change 1 'face)))
      (kill-buffer " ")
      (print result)))))

;;; Tests for previous-single-property-change

;; Test with no properties
(deftestf 'pspc-no-properties ('nil)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (let ((result (previous-single-property-change 10 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test with single interval
(deftestf 'pspc-single-interval (1)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 6 'face 'bold)
    (let ((result (previous-single-property-change 6 'face)))
      (kill-buffer " ")
      (print result)))))

;; Test from after all properties
(deftestf 'pspc-after-properties (6)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 6 'face 'bold)
    (let ((result (previous-single-property-change 10 'face)))
      (kill-buffer " ")
      (print result)))))

;;; Tests for next-property-change (any property)

;; Test with single property
(deftestf 'npc-single-property (6)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 6 'face 'bold)
    (let ((result (next-property-change 1)))
      (kill-buffer " ")
      (print result)))))

;; Test with multiple properties changing at different positions
(deftestf 'npc-multiple-properties (4)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 4 'face 'bold)
    (put-text-property 1 8 'font-lock-face 'keyword)
    (let ((result (next-property-change 1)))
      (kill-buffer " ")
      (print result)))))

;;; Edge cases

;; Test position exactly at property boundary
(deftestf 'nspc-at-boundary (8)
  (elfmt `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
    (erase-buffer)
    (princ "hello world" (current-buffer))
    (put-text-property 1 5 'face 'bold)
    (put-text-property 5 8 'face 'italic)
    (let ((result (next-single-property-change 5 'face)))
      (kill-buffer " ")
      (print result)))))
