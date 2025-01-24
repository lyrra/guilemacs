;;;; guiles limits can be found with:
;; (use-modules (rnrs arithmetic fixnums))
;; (format (current-error-port) "~s~%" (fixnum-width)) ; => 62
;; (format (current-error-port) "~s~%" (greatest-fixnum)) ; => 2305843009213693951

(let ((fx (- (expt 2 61) 1)))
  (deftestf 'print-most-positive-fixnum (fx)
    (el-expr `(print ,fx))))

(let ((fx (- (expt 2 61) 1))) ; at limit, this becomes a two-complements most-negative-fixnum
  (deftestf 'print-most-negative-fixnum (fx)
    (el-expr `(print ,fx))))

(let ((fx (- (expt 2 62) 1)))
  (deftestf 'print-least-negative-fixnum (fx)
    (el-expr `(print ,fx))))

(let ((bs (- (expt 2 62) 2)))
  (deftestf 'print-penultimate-least-negative-fixnum (bs)
    (el-expr `(print ,bs))))
