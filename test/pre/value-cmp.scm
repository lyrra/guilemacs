
(deftest value-lt-0i1i (t)
  (el-expr '(princ (value< 0 1))))

(deftest value-lt-1i0i (nil)
  (el-expr '(princ (value< 1 0))))

(deftest value-lt-1i1i (nil)
  (el-expr '(princ (value< 1 1))))


(deftest value-lt-0f1f (t)
  (el-expr '(princ (value< 0.0 1.0))))

(deftest value-lt-1f0f (nil)
  (el-expr '(princ (value< 1.0 0.0))))

(deftest value-lt-1f1f (nil)
  (el-expr '(princ (value< 1.0 1.0))))
