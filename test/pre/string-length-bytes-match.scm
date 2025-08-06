; use make-string in the tests to by-pass the lisp readers string handling

(deftest string-length-ascii (ok)
  (el-expr `(let ((ascii-str "\"a\""))
              (if (equal 1 (length ascii-str))
                  (print 'ok)))))

(deftest string-length-utf8 (ok)
  (el-expr `(let ((utf8-str "\"λ\""))
              (if (equal 1 (length utf8-str))
                  (print 'ok)))))

(deftest string-length-utf8-make-string (ok)
  (el-expr `(let ((utf8-str (make-string 1 955)))  ; λ is Unicode 955
              (if (equal 1 (length utf8-str))
                  (print 'ok)))))

;

(deftest string-bytes-ascii (ok)
  (el-expr `(let ((ascii-str "\"a\""))
              (if (equal 1 (string-bytes ascii-str))
                  (print 'ok)))))

(deftest string-bytes-utf8 (ok)
  (el-expr `(let ((utf8-str "\"λ\""))
              (if (equal 2 (string-bytes utf8-str))
                  (print 'ok)))))

(deftest string-bytes-utf8-make-string (ok)
  (el-expr `(let ((utf8-str (make-string 1 955)))  ; λ is Unicode 955
              (if (equal 2 (string-bytes utf8-str))
                  (print 'ok)))))

;

(deftest string-match-ascii (ok)
  (el-expr `(let ((ascii-str "\"a\""))
              (if (equal 0 (string-match "\"a\"" ascii-str))
                  (print 'ok)))))

(deftest string-match-utf8 (ok)
  (el-expr `(let ((utf8-str "\"λ\""))
              (if (equal 0 (string-match "\"λ\"" utf8-str))
                  (print 'ok)))))

(deftest string-match-utf8-make-string (ok)
  (el-expr `(let ((utf8-str-a (make-string 1 955))  ; λ is Unicode 955
                  (utf8-str-b (make-string 1 955)))
              (if (equal 0 (string-match utf8-str-a utf8-str-b))
                  (print 'ok)))))
