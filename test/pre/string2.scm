
(deftest string-reverse ("abc")
  (el-expr `(let ((x "\"cba\""))
              (print (reverse x)))))

(deftest compare-strings-ss (t)
  (el-expr `(print (compare-strings "\"Test\"" nil nil "\"test\"" nil nil t))))

(let ((emit-test (lambda (t1 t2 ignore-case e)
                   (match (list t1 t2)
                     (((str1 start1 end1) (str2 start2 end2))
                      (deftestf 'compare-strings-ns (e)
                        (el-expr `(print (compare-strings
                                           ,str1
                                           ,start1 ; defaults to 0
                                           ,end1 ; defaults to length of string

                                           ,str2
                                           ,start2 ; defaults to 0
                                           ,end2 ; defaults to length of string

                                           ,ignore-case)))))))))
  (let ((s "\"a\"")
        (l 1))
    (emit-test ; first string triplet :: (string start end)
               (list s
                     (if (= 0 (random 2)) 'nil 0)
                     (if (= 0 (random 2)) 'nil l))
               ; second string triplet
               (list s
                     (if (= 0 (random 2)) 'nil 0)
                     (if (= 0 (random 2)) 'nil l))
               ; ignore-case
               (if (= 0 (random 2)) 'nil 't)
               ; expected result
               't)))
