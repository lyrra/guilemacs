;;; int int

(deftest value-lt-0i1i (t)
  (el-expr '(princ (value< 0 1))))

(deftest value-lt-1i0i (nil)
  (el-expr '(princ (value< 1 0))))

(deftest value-lt-1i1i (nil)
  (el-expr '(princ (value< 1 1))))

;;; float float

(deftest value-lt-0f1f (t)
  (el-expr '(princ (value< 0.0 1.0))))

(deftest value-lt-1f0f (nil)
  (el-expr '(princ (value< 1.0 0.0))))

(deftest value-lt-1f1f (nil)
  (el-expr '(princ (value< 1.0 1.0))))

;;; int float

(deftest value-lt-0i1f (t)
  (el-expr '(princ (value< 0 1.0))))

(deftest value-lt-1i0f (nil)
  (el-expr '(princ (value< 1 0.0))))

(deftest value-lt-1i1f (nil)
  (el-expr '(princ (value< 1 1.0))))

;;; float int

(deftest value-lt-0f1i (t)
  (el-expr '(princ (value< 0.0 1))))

(deftest value-lt-1f0i (nil)
  (el-expr '(princ (value< 1.0 0))))

(deftest value-lt-1f1i (nil)
  (el-expr '(princ (value< 1.0 1))))


;;;;
;;;; repeat above tests, but test bignum against int and float
;;;;
;;;; using (expt 2 64) which wont fit into a (tagged) fixnum

(let ((bs (expt 2 64))
      (bl (1+ (expt 2 64))))

  ;; int bignum
  (deftest value-lt-1ib (t)
    (el-expr `(princ (value< 1 ,bs))))

  ;; bignum int
  (deftest value-lt-b1i (nil)
    (el-expr `(princ (value< ,bs 1))))

  ;; float bignum
  (deftest value-lt-1fb (t)
    (el-expr `(princ (value< 1.0 ,bs))))

  ;; bignum float
  (deftest value-lt-b1f (nil)
    (el-expr `(princ (value< ,bs 1.0))))

  ;; bignum-small bignum-large
  (deftest value-lt-bsbl (t)
    (el-expr `(princ (value< ,bs ,bl))))

  (deftest value-lt-blbs (nil)
    (el-expr `(princ (value< ,bl ,bs)))))
