;; Test the type predicate functions we've migrated

;; Test numberp function
(deftest numberp-integer (t)
  (el-expr `(print (numberp 42))))

(deftest numberp-float (t)
  (el-expr `(print (numberp 3.14))))

(deftest numberp-string (nil)
  (el-expr `(print (numberp "\"hello\""))))

;; Test integerp function
(deftest integerp-integer (t)
  (el-expr `(print (integerp 42))))

(deftest integerp-float (nil)
  (el-expr `(print (integerp 3.14))))

;; Test floatp function
(deftest floatp-float (t)
  (el-expr `(print (floatp 3.14))))

(deftest floatp-integer (nil)
  (el-expr `(print (floatp 42))))

;; Test vectorp function
(deftest vectorp-vector (t)
  (el-expr `(print (vectorp "[1 2 3]"))))

(deftest vectorp-list (nil)
  (el-expr `(print (vectorp '(1 2 3)))))

;; Test symbolp function
(deftest symbolp-symbol (t)
  (el-expr `(print (symbolp 'hello))))

(deftest symbolp-string (nil)
  (el-expr `(print (symbolp "\"hello\""))))
