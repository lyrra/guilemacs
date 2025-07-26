
(deftest string-reverse ("abc")
  (el-expr `(let ((x "\"cba\""))
              (print (reverse x)))))

(deftest compare-strings-ss (t)
  (el-expr `(print (compare-strings "\"Test\"" nil nil "\"test\"" nil nil t))))

(let ((s "\"a\""))
  (deftestf 'compare-strings-ns ('t)
    (el-expr `(print (compare-strings ,s    ; str1
                                      0     ; start1 -- defaults to 0
                                      nil   ; end1   -- defaults to length of string
                                      ,s    ; str2
                                      0     ; start2 -- defaults to 0
                                      nil   ; end2   -- defaults to length of string
                                      nil   ; ignore_case
                                      )))))
