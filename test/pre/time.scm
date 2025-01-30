
(define %interesting-time-numbers
        (list 0 -2 1 0.0 -0.0 -2.0 1.0
             '(0 1 0 0) '(1 0 0 0) '(-1 0 0 0)
             '(123456789000000 . 1000000)
             (cons (1+ most-positive-fixnum) 1000000000000)
             ))

(define %interesting-time-numbers2
        (list 0 -2 1 0.0 -0.0 -2.0 1.0
        ; most-negative-fixnum
        ; most-positive-fixnum
        ; (1- most-negative-fixnum)
        ; (1+ most-positive-fixnum)
        '(0 1 0 0) '(1 0 0 0) '(-1 0 0 0)
        '(123456789000000 . 1000000)
        (cons (1+ most-positive-fixnum) 1000000000000)
        ; (cons 1000000000000 (1+ most-positive-fixnum))
        ))

(deftestf 'time-convert  ('(7881299347898368 . 2251799813685248))
  (el-expr `(print (time-convert 3.5 t))))

(deftest time-convert-hanoi (t)
  (el-expr `(print (integerp (time-convert nil 'integer)))))

; trigger call to ticks_hz_list4
(deftest time-convert-0125 ((0 0 0 0))
  (el-expr `(print (time-convert 0.125 'list))))

; trigger call to ticks_hz_list4
(deftest time-convert-ticks_hz_list4 ((0 123 0 123))
  (el-expr `(print (time-convert 123 'list))))
; trigger call to ticks_hz_list4
(deftest time-convert-ticks_hz_list4-2 ((1876831054 45057 123000000 1))
  (el-expr `(print (time-convert 123000000000000.9999 'list))))

;(deftest time-convert-ticks_hz_hz_ticks ((12300000000000100 . 100))
;  (el-expr `(print (time-convert 123000000000000.9999 100))))

(deftest time-convert-ticks_hz_hz_ticks ((12300000000000100000000000 . 100000000000))
  (el-expr `(print (time-convert 123000000000000.9999 100000000000))))

(deftestf 'decode-time ('(0 0 1 1 1 1970 4 nil 3600))
  (el-expr `(print (decode-time 0))))

(deftestf 'format-time-string ("1970-01-01T01:00:03+0100")
  (el-expr `(print (format-time-string "\"%FT%T%z\"" (time-convert 3.5 t)))))

(deftestf 'format-time-string ("2025-01-28T13:50:16+0100")
  (el-expr `(print (format-time-string "\"%FT%T%z\"" 1738068616.6339903))))

; cant run test, emacs aborts
;(deftestf 'decode-time-bignum (text "Specified time is not representable")
;  (el-expr `(print (decode-time ,(- (expt 2 61) (expt 2 60))))))

'(deftestf 'decode-time-1 ('(0 0 1 1 1 1970 4 nil 3600))
  (el-expr `(print (decode-time 0.123 nil t))))

'(deftestf 'decode-time-0 ('(0 0 1 1 1 1970 4 nil 3600))
  (el-expr `(print (decode-time 16140901064495857663 t 'integer))))

(for-each (lambda (trip)
            (let ((emit-test (lambda (a b r)
                   (deftestf (format #f "time-equal-p_~a_~a_~a" a b r)
                     (r)
                     (el-expr `(print (time-equal-p ,a ,b)))))))
              (match trip
                ((a b)
                 (emit-test a a 't)
                 (emit-test b b 't)
                 (emit-test a b 'nil)))))
          `((16140901064495857663 0)
            (,(expt 2 60) 0)
            (,(expt 2 60) ,(expt 2 61))))

;; based on ERT test decode-then-encode-time
(for-each
 (lambda (a)
   (deftestf (format #f "decode-then-encode-time_~a" a)
             ('t)
     (el-expr `(let* ((a ',a)
                      (d (decode-time a t t))
                      (e (if d (encode-time d))))
                 (print (time-equal-p a e))))))
 %interesting-time-numbers)
(for-each
 (lambda (a)
   (deftestf (format #f "decode-then-encode-time_int_~a" a)
             ('t)
     (el-expr `(let* ((a ',a)
                      (d-integer (decode-time a t 'integer))
                      (e-integer (if d-integer (encode-time d-integer))))
                 (print (time-equal-p (time-convert a 'integer)
                                      e-integer))))))
 %interesting-time-numbers2)

(deftestf 'time-less-p ('t)
  (el-expr `(print (time-less-p 0 '(26510 8973 916267 104000)))))
