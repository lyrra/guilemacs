
(deftest string-reverse ("abc")
  (el-expr `(let ((x "\"cba\""))
              (print (reverse x)))))

(deftest compare-strings-ss (t)
  (el-expr `(print (compare-strings "\"Test\"" nil nil "\"test\"" nil nil t))))

(let ((emit-test (lambda (s e)
                   (deftestf 'compare-strings-ns (e)
                     (el-expr `(print (compare-strings ,s    ; str1
                                                       ; start1 -- defaults to 0
                                                       ,(if (= 0 (random 2)) 'nil 0)
                                                       ; end1   -- defaults to length of string
                                                       ,(if (= 0 (random 2)) 'nil 1)

                                                       ,s    ; str2
                                                       ; start2 -- defaults to 0
                                                       ,(if (= 0 (random 2)) 'nil 0)
                                                       ; end2   -- defaults to length of string
                                                       ,(if (= 0 (random 2)) 'nil 1)

                                                       ; ignore_case
                                                       nil)))))))
  (emit-test "\"a\"" 't))
