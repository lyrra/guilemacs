
; test endianess
(deftest byteorder (t)
  (el-expr `(let ((x (byteorder)))
              (print (or (= x 66) (= x 108))))))
