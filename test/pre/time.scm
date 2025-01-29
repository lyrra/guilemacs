
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
