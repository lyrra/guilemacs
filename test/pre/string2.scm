
(deftest string-reverse ("abc")
  (el-expr `(let ((x "\"cba\""))
              (print (reverse x)))))

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
                        (if (= 0 (random 2)) 'nil 0)
                        (if (= 0 (random 2)) 'nil len))
                  ; second string triplet
                  (list str
                        (if (= 0 (random 2)) 'nil 0)
                        (if (= 0 (random 2)) 'nil len))
                  ; ignore-case
                  (if (= 0 (random 2)) 'nil 't)
                  ; expected result
                  't))))
   ; we need to pass the length, if calculated it would count the escaped chars
   ; though we can't use the length to test substring matching (FIX:)
   '((compare-strings-1 ("\"a\"" 1))
     (compare-strings-2 ("\"Test\"" 4)))))
