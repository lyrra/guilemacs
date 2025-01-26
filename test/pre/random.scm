
(deftest random-fixnum (t)
  (el-expr `(print (integerp (random most-positive-fixnum)))))
