
(deftest string-reverse ("abc")
  (el-expr `(let ((x "\"cba\""))
              (print (reverse x)))))

;; Elisp nil is an empty fragment in string concatenation.
(deftest concat-nil-string-fragments ("left-right")
  (el-expr `(print (concat nil "\"left\"" nil "\"-\""
                           "\"right\"" nil))))

;; replace-match builds its result with concat2/concat3.  In particular,
;; \& at the start of NEWTEXT must not expose nil as literal text.
(deftest replace-match-nil-concat-fragments ("S-down-mouse-2")
  (el-expr `(let ((str "\"S-mouse-2\""))
              (string-match "\"\\\\`S-\"" str)
              (print (replace-match "\"\\\\&down-\"" t nil str)))))

(let ((emit-test (lambda (name t1 t2 ignore-case e)
                   (match (list t1 t2)
                     (((str1 start1 end1) (str2 start2 end2))
                      (deftestf name (e)
                        (el-expr `(print (compare-strings
                                           ,str1
                                           ,start1 ; defaults to 0
                                           ,end1 ; defaults to length of string

                                           ,str2
                                           ,start2 ; defaults to 0
                                           ,end2 ; defaults to length of string

                                           ,ignore-case)))))))))
  (for-each (lambda (lst)
              (match lst
                ((name (str len))
                 (emit-test
                  name
                  ; first string triplet :: (string start end)
                  (list str
                        (rand-pick '(nil 0))
                        (rand-pick `(nil ,len)))
                  ; second string triplet
                  (list str
                        (rand-pick '(nil 0))
                        (rand-pick `(nil ,len)))
                  ; ignore-case
                  (rand-pick '(nil t))
                  ; expected result
                  't))))
   ; we need to pass the length, if calculated it would count the escaped chars
   ; though we can't use the length to test substring matching (FIX:)
   '((compare-strings-1 ("\"a\"" 1))
     (compare-strings-2 ("\"Test\"" 4)))))
