
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

(deftest time-convert (78796799)
  (el-expr `(print
             (time-convert '(1202 22527 999999 999999) 'integer))))

(deftest time-convert-hanoi (t)
  (el-expr `(print (integerp (time-convert nil 'integer)))))

; trigger call to ticks_hz_list4
(deftest time-convert-0125 ((0 0 125000 0))
  (el-expr `(print (time-convert 0.125 'list))))

; trigger call to ticks_hz_list4
(deftest time-convert-ticks_hz_list4 ((0 123 0 0))
  (el-expr `(print (time-convert 123 'list))))
; trigger call to ticks_hz_list4
(deftest time-convert-ticks_hz_list4-2 ((1876831054 45057 0 0))
  (el-expr `(print (time-convert 123000000000000.9999 'list))))

;(deftest time-convert-ticks_hz_hz_ticks ((12300000000000100 . 100))
;  (el-expr `(print (time-convert 123000000000000.9999 100))))

(deftest time-convert-ticks_hz_hz_ticks ((12300000000000100000000000 . 100000000000))
  (el-expr `(print (time-convert 123000000000000.9999 100000000000))))

(deftest time-subtract ((999999999999 . 1000000000000))
  (el-expr `(print (time-subtract '(78796799999999999999 . 1000000000000)
                                  '(78796799000000000000 . 1000000000000)))))

(deftest time-subtract ((78796799000000000000 . 1000000000000))
  (el-expr `(print
             (let* ((look '(1202 22527 999999 999999))
                    (look-ticks-hz (time-convert look t))
                    (hz (cdr look-ticks-hz))
                    (look-integer (time-convert look 'integer))
                    (sec ;(time-subtract look-ticks-hz
                         (time-convert look-integer hz)))
             sec))))

(deftest time-subtract ((59999999999999 . 1000000000000))
  (el-expr `(print
             (let* ((look '(1202 22527 999999 999999))
                    (look-ticks-hz (time-convert look t))
	            (hz (cdr look-ticks-hz))
	            (look-integer (time-convert look 'integer))
	            (sec (time-add (time-convert 59 hz)
			           (time-subtract look-ticks-hz
					          (time-convert look-integer hz)))))
               sec))))

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

(deftest format-time-string-with-zone (((equal ((59999999999999 . 1000000000000) 59 23 30 6 1972 5 nil 0) ((59999999999999 . 1000000000000) 59 15 30 6 1972 5 nil -28800)) (equal (59 59 23 30 6 1972 5 nil 0) (59 59 15 30 6 1972 5 nil -28800))))
  (el-expr
   `(let* ((look '
                  ;(1202 22527 999999 999999)
                  ;(7879679999900 . 100000)
                  (78796799999999999999 . 1000000000000)
                  )
           (look-ticks-hz (time-convert look t))
	   (hz (cdr look-ticks-hz))
	   (look-integer (time-convert look 'integer))
	   (sec (time-add (time-convert 59 hz)
			  (time-subtract look-ticks-hz
					 (time-convert look-integer hz)))))
      (let ((zone '(-28800 "\"PST\""))
            (decoded-time (list sec 59 15 30 6 1972 5 nil -28800)))
        (print (list (list 'equal (decode-time look zone t) decoded-time)
                     (list 'equal (decode-time look zone 'integer)
	                   (cons (time-convert (car decoded-time) 'integer)
		                 (cdr decoded-time)))))))))

(for-each (lambda (ae)
            (match ae
              ((a e)
               (deftestf (format #f "decode-then-encode-time-~a" a) (e)
                 (el-expr `(print
                            (let* ((a ',a)
                                   (d (decode-time a t t))
                                   (d-integer (decode-time a t 'integer))
	                           (e (encode-time d))
	                           (e-integer (encode-time d-integer)))
                              (list d
                                    d-integer
                                    (time-equal-p a e)
	                            (time-equal-p (time-convert a 'integer)
                                                  e-integer)))))))))

          `((0 ((0 0 0 1 1 1970 4 nil 0) (0 0 0 1 1 1970 4 nil 0) t t))
            (-2 ((58 59 23 31 12 1969 3 nil 0) (58 59 23 31 12 1969 3 nil 0) t t))
            (1 ((1 0 0 1 1 1970 4 nil 0) (1 0 0 1 1 1970 4 nil 0) t t))
            (0.0 ((0 0 0 1 1 1970 4 nil 0) (0 0 0 1 1 1970 4 nil 0) t t))
            (-0.0 ((0 0 0 1 1 1970 4 nil 0) (0 0 0 1 1 1970 4 nil 0) t t))
            (-2.0 (((130604389193744384 . 2251799813685248) 59 23 31 12 1969 3 nil 0) (58 59 23 31 12 1969 3 nil 0) t t))
            (1.0 (((4503599627370496 . 4503599627370496) 0 0 1 1 1970 4 nil 0) (1 0 0 1 1 1970 4 nil 0) t t))
            ;most-negative-fixnum most-positive-fixnum
            ;(- most-negative-fixnum 1)
            ;(+ most-positive-fixnum 1)
            ((0 1 0 0) (((1000000000000 . 1000000000000) 0 0 1 1 1970 4 nil 0) (1 0 0 1 1 1970 4 nil 0) t t))
            ((1 0 0 0) (((16000000000000 . 1000000000000) 12 18 1 1 1970 4 nil 0) (16 12 18 1 1 1970 4 nil 0) t t))
            ((-1 0 0 0) (((44000000000000 . 1000000000000) 47 5 31 12 1969 3 nil 0) (44 47 5 31 12 1969 3 nil 0) t t))
            ((123456789000000 . 1000000) (((9000000 . 1000000) 33 21 29 11 1973 4 nil 0) (9 33 21 29 11 1973 4 nil 0) t t))
            ;(((+ ,most-positive-fixnum 1) . 1000000000000) t)
            ;((1000000000000 . (+ most-positive-fixnum 1)) t)
            ))


(deftestf 'time-less-p ('t)
  (el-expr `(print (time-less-p 0 '(26510 8973 916267 104000)))))

(deftestf 'float-time-precision-1 ('(t t t t))
  (el-expr `(print (list (= (float-time '(0 1 0 4025)) 1.000000004025)
                         (= (float-time '(1000000004025 . 1000000000000)) 1.000000004025)
                         (< 0 (float-time '(1 . 10000000000)))
                         (< (float-time '(-1 . 10000000000)) 0)))))

(deftest float-time-1 (-0.002375)
  (el-expr `(print (float-time '(-5476377146882523 . 2305843009213693952)))))
