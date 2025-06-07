
(deftest string-reverse ("abc")
  (el-expr `(let ((x "\"cba\""))
              (print (reverse x)))))

(deftest compare-strings-ss (t)
  (el-expr `(print (compare-strings "\"Test\"" nil nil "\"test\"" nil nil t))))

(deftest compare-strings-ns (t)
  (el-expr `(print (compare-strings nil 0 nil "\"a\"" 0 nil nil))))
