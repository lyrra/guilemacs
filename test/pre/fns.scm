(for-each (lambda (pair)
            (match pair
              ((name input expected)
               (deftestf name (expected)
                 (el-expr `(let ((x ,input))
                             (print (atom x))))))))
  '(
    (atom-42 42 t)
    (atom-symbol 'symbol t)
    (atom-nil nil t)
    (atom-list '(a b) nil)
    ))

; test endianess
(deftest byteorder (t)
  (el-expr `(let ((x (byteorder)))
              (print (or (= x 66) (= x 108))))))
