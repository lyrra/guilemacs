;; Test cases for text property navigation functions
;; Tests for next-single-property-change, previous-single-property-change, etc.
;; Using princ with buffer as stream to insert text (insert depends on elisp code)

(let-syntax
  ((frob
    (syntax-rules ()
      ((_ name res expr-1 expr-2)
       (deftest name (res)
         (elfmt `(progn
                  (set-buffer (get-buffer-create (generate-new-buffer-name " ") nil))
                  (erase-buffer)
                  (insert "hello world")
                  expr-1
                  (let ((result expr-2))
                    (kill-buffer " ")
                    (print result)))))))))
  (frob nspc-no-properties nil
        nil
        (next-single-property-change 1 'face))
  ;; Test with single interval - should return end of interval
  (frob nspc-single-interval 6
        (put-text-property 1 6 'face 'bold)
        (next-single-property-change 1 'face))
  ;; Test from middle of interval
  (frob nspc-middle-of-interval 6
        (put-text-property 1 6 'face 'bold)
        (next-single-property-change 3 'face))
  ;; Test with two contiguous intervals with SAME value
  ;; This is the bug case - should skip to end of both intervals
  (frob nspc-contiguous-same-value 9
        (progn
         (put-text-property 1 5 'face 'bold)
         (put-text-property 5 9 'face 'bold))
        (next-single-property-change 1 'face))
  ;; Test with two contiguous intervals with DIFFERENT values
  (frob nspc-contiguous-different-value 5
        (progn
         (put-text-property 1 5 'face 'bold)
         (put-text-property 5 9 'face 'italic))
        (next-single-property-change 1 'face))
  ;; Test with gap between intervals
  (frob nspc-with-gap 4
        (progn
         (put-text-property 1 4 'face 'bold)
         (put-text-property 7 10 'face 'italic))
        (next-single-property-change 1 'face))
  ;; Test from position before any properties
  (frob nspc-before-properties 5
        (put-text-property 5 8 'face 'bold)
        (next-single-property-change 1 'face))
  ;; Test with limit - should not go past limit
  (frob nspc-with-limit 4
        (put-text-property 1 8 'face 'bold)
        (next-single-property-change 1 'face nil 4))
  ;; Test with multiple properties - only check one
  (frob nspc-multiple-properties 5
        (progn
         (put-text-property 1 5 'face 'bold)
         (put-text-property 1 8 'font-lock-face 'keyword))
        (next-single-property-change 1 'face))
  ;; Test with three contiguous intervals with same value
  (frob nspc-three-contiguous-same 10
        (progn
         (put-text-property 1 4 'face 'bold)
         (put-text-property 4 7 'face 'bold)
         (put-text-property 7 10 'face 'bold))
        (next-single-property-change 1 'face))

  ;;; Tests for previous-single-property-change

  ;; Test with no properties
  (frob pspc-no-properties nil
        nil
        (previous-single-property-change 10 'face))

  ;; Test with single interval
  (frob pspc-single-interval 1
        (put-text-property 1 6 'face 'bold)
        (previous-single-property-change 6 'face))

  ;; Test from after all properties
  (frob pspc-after-properties 6
        (put-text-property 1 6 'face 'bold)
        (previous-single-property-change 10 'face))

  ;;; Tests for next-property-change (any property)

  ;; Test with single property
  (frob npc-single-property 6
        (put-text-property 1 6 'face 'bold)
        (next-property-change 1))

  ;; Test with multiple properties changing at different positions
  (frob npc-multiple-properties 4
        (progn
         (put-text-property 1 4 'face 'bold)
         (put-text-property 1 8 'font-lock-face 'keyword))
        (next-property-change 1))

  ;;; Edge cases

  ;; Test position exactly at property boundary
  (frob nspc-at-boundary 8
        (progn
         (put-text-property 1 5 'face 'bold)
         (put-text-property 5 8 'face 'italic))
        (next-single-property-change 5 'face))

  ;;
  )
