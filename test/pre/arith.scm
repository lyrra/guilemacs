
;; note, if not doing indirect by passing through a variable
;; and instead doing direct like (/ ,n 3) , guile compiler
;; will optimize that away into a rational (fractional), and
;; that type isn't supported by guilemacs

;; next, emacs divide is like c, if you pass it exact integers
;; it will truncate, as demonstrated in this test:
(deftestf 'divide (0)
  (el-expr `(let ((n 1))
    (print (/ n 3)))))

(for-each (lambda (p)
            (match p
              ((n e)
               (deftestf 'divide (e)
                 (el-expr `(let ((n ,n))
                             (print (list (-     (/ n 3))
                                          (- n 1 (/ n 3))))))))))
  '((0 (0 -1))
    (1 (0 0))
    (2 (0 1))
    (3 (-1 1))
    (10 (-3 6))
    (100 (-33 66))
    (1000 (-333 666))
    (10.1 (-3.3666666666666667 5.7333333333333325))))

;; test covers completion--flex-score-1
(deftestf 'divide-promote-float (0.3333333333333333)
  (el-expr `(let ((a 1)
                  (b 3))
              (print (/ a b 1.0)))))

(deftestf 'plus (0)
  (el-expr `(print (+))))

(deftestf 'plus (1)
  (el-expr `(let ((a 1))
              (print (+ a)))))

(deftestf 'plus (text "1.8446744073709552e+19")
  (el-expr `(let ((a 0)
                  (b 1)
                  (c 0.0000000001)
                  (d (ash 1 64)))
              (print (+ a b c d)))))

(deftestf 'times (1)
  (el-expr `(print (*))))

(deftestf 'times (2)
  (el-expr `(let ((a 2))
              (print (* a)))))

(deftestf 'times (text "3689348814.7419105")
  (el-expr `(let ((a 1)
                  (b 2)
                  (c 0.0000000001)
                  (d (ash 1 64)))
              (print (* a b c d)))))

(for-each (lambda (tri)
            (match tri
              ((x y e)
               (deftestf 'ceiling (e)
                 (el-expr `(let ((x ,x)
                                 (y ,y))
                             (print (ceiling x y))))))))
          `((10 3 4)
            (10 -3 -3)
            (-10 3 -3)
            (-10 -3 4)
            (9.0001 3 4)
            (-11.9999 3 -3)
            (10 -3.3334 -2)))

(for-each (lambda (tri)
            (match tri
              ((x y e)
               (deftestf 'floor (e)
                 (el-expr `(let ((x ,x)
                                 (y ,y))
                             (print (floor x y))))))))
          `((10 3 3)
            (10 -3 -4)
            (-10 3 -4)
            (-10 -3 3)
            (9.0001 3 3)
            (-11.9999 3 -4)
            (10 -3.3334 -3)))

(for-each (lambda (tri)
            (match tri
              ((x y e)
               (deftestf 'round (e)
                 (el-expr `(let ((x ,x)
                                 (y ,y))
                             (print (round x y))))))))
          `((10 3 3)
            (10 -3 -3)
            (-10 3 -3)
            (-10 -3 3)
            (9.0001 3 3)
            (-11.9999 3 -4)
            (10 -3.3334 -3)))

(for-each (lambda (tri)
            (match tri
              ((x y e)
               (deftestf 'truncate (e)
                 (el-expr `(let ((x ,x)
                                 (y ,y))
                             (print (truncate x y))))))))
          `((10 3 3)
            (10 -3 -3)
            (-10 3 -3)
            (-10 -3 3)
            (9.0001 3 3)
            (-11.9999 3 -3)
            (10 -3.3334 -2)))

(for-each (lambda (tri)
            (match tri
              ((fun x e)
               (deftestf fun (e)
                 (el-expr `(let ((x ,x))
                             (print (,fun x))))))))
          `((ftruncate 10.5 10.0)
            (fceiling  10.5 11.0)
            (ffloor    10.5 10.0)
            (fround     10.0 10.0)
            (fround    10.5 10.0)))

(for-each (lambda (tri)
            (match tri
              ((x y e)
               (deftestf 'mod (e)
                 (el-expr `(let ((x ,x)
                                 (y ,y))
                             (print (mod x y))))))))
          `((10   3   1)
            (10.0 3.0 1.0)
            ( 1.0 3.0 1.0)
            ( 0   1   0)
            ;; note this fails on guile, perhaps due to keeping float and hit by precision
            ;(,(ash 1 64)  999999999.0  156295708.0)
            ; ensure we use guiles euclidean-remainder if dealing with floats
            (0.3333333333333333 1 0.3333333333333333)
            (-0.3333333333333333 1 0.6666666666666667)))

(deftestf 'remainder (-1)
  (el-expr `(let ((a -1))
              (print (% a 2)))))
