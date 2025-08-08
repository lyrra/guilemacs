(deftest clear-string-basic (nil)
  (el-expr `(progn
    (let ((test-string "\"hello world\""))
      (clear-string test-string)
      (print 'nil)))))

(deftest clear-string-utf8 (nil)
  (el-expr `(progn
    (let ((test-string "\"λελλο κοσμε\""))
      (clear-string test-string)
      (print 'nil)))))

(deftest clear-string-empty (nil)
  (el-expr `(progn
    (let ((test-string "\"\""))
      (clear-string test-string)
      (print 'nil)))))

(deftest clear-string-mixed (nil)
  (el-expr `(progn
    (let ((test-string "\"ASCII中文🌟\""))
      (clear-string test-string)
      (print 'nil)))))

(deftest clear-string-result (nil)
  (el-expr `(progn
    (let ((test-string (make-string 10 ?x)))
      (clear-string test-string)
      (print 'nil)))))