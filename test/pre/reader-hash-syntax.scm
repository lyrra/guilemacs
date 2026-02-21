;;; Test file for Guile reader #s(...) hash-table and record syntax
;;; This tests that hash-tables and records are read correctly

;; Test read-from-string basic functionality
(let-syntax ((emit-read-test
              (syntax-rules ()
                ((_ name str expected)
                 (deftest name (expected)
                   (el-expr `(print (car (read-from-string ,str)))))))))

  ;; Basic types
  (emit-read-test read-symbol "foo" foo)
  (emit-read-test read-number "42" 42)
  (emit-read-test read-negative "-17" -17)
  (emit-read-test read-float "3.14" 3.14)
  (emit-read-test read-string "hello" "hello")
  (emit-read-test read-nil "nil" nil)
  (emit-read-test read-t "t" t)

  ;; Lists
  (emit-read-test read-empty-list "()" nil)
  (emit-read-test read-simple-list "(a b c)" (a b c))
  (emit-read-test read-nested-list "((a b) (c d))" ((a b) (c d)))
  (emit-read-test read-dotted-pair "(a . b)" (a . b))

  ;; Vectors
  (emit-read-test read-vector "[1 2 3]" "[1 2 3]")
  (emit-read-test read-empty-vector "[]" "[]")

  ;; Quote syntax
  (emit-read-test read-quote "'foo" (quote foo))
  (emit-read-test read-backquote "`foo" (\` foo))
  (emit-read-test read-unquote ",foo" (\, foo))
  (emit-read-test read-splice ",@foo" (\,@ foo))
  )

;; Test read-from-string position tracking
(let-syntax ((emit-pos-test
              (syntax-rules ()
                ((_ name str expected-pos)
                 (deftestf 'name (expected-pos)
                   (el-expr `(cdr (read-from-string ,str))))))))

  (emit-pos-test read-pos-symbol "foo" 3)
  (emit-pos-test read-pos-number "12345" 5)
  (emit-pos-test read-pos-string "hi" 4)
  (emit-pos-test read-pos-with-space "\"  foo" 5)
  (emit-pos-test read-pos-list "(a b)" 5)
  )

;; Test read-from-string with start/end parameters
(let-syntax ((emit-substr-test
              (syntax-rules ()
                ((_ name str start end expected)
                 (deftestf 'name (expected)
                   (el-expr `(car (read-from-string ,str ,start ,end))))))))

  (emit-substr-test read-substr-middle "xxxfooyyy" 3 6 foo)
  (emit-substr-test read-substr-start "123abc" 0 3 123)
  (emit-substr-test read-substr-end "abc456" 3 6 456)
  )

;; Test #s(hash-table ...) syntax
(let-syntax ((emit-hash-test
              (syntax-rules ()
                ((_ name str key expected-val)
                 (deftestf 'name (expected-val)
                   (el-expr `(gethash (quote ,key)
                                      (car (read-from-string ,str)))))))))

  ;; Basic hash-table reading
  (emit-hash-test hash-simple "#s(hash-table data (a 1 b 2))" a 1)
  (emit-hash-test hash-simple-b "#s(hash-table data (a 1 b 2))" b 2)

  ;; Hash-table with test parameter
  (emit-hash-test hash-with-test "#s(hash-table test equal data (x\" 10))" "x" 10)

  ;; Empty hash-table
  )

;; Test hash-table type checking
(deftestf 'hash-is-hash-table (t)
  (el-expr `(hash-table-p (car (read-from-string "#s(hash-table data (a 1))")))))

(deftestf 'hash-empty-is-hash-table (t)
  (el-expr `(hash-table-p (car (read-from-string "#s(hash-table)")))))

(deftestf 'hash-count-simple (2)
  (el-expr `(hash-table-count (car (read-from-string "#s(hash-table data (a 1 b 2))")))))

(deftestf 'hash-count-empty (0)
  (el-expr `(hash-table-count (car (read-from-string "#s(hash-table)")))))

;; Test #s(record ...) syntax - records are represented as vectors with type in slot 0
(deftestf 'record-is-vector (t)
  (el-expr `(vectorp (car (read-from-string "#s(my-record field1 field2)")))))

(deftestf 'record-type-slot (my-record)
  (el-expr `(aref (car (read-from-string "#s(my-record f1 f2)")) 0)))

(deftestf 'record-field1 (f1)
  (el-expr `(aref (car (read-from-string "#s(my-record f1 f2)")) 1)))

(deftestf 'record-field2 (f2)
  (el-expr `(aref (car (read-from-string "#s(my-record f1 f2)")) 2)))

(deftestf 'record-length (3)
  (el-expr `(length (car (read-from-string "#s(my-record a b)")))))

;; Test complex hash-table data
(deftestf 'hash-nested-value (42)
  (el-expr `(car (gethash 'key (car (read-from-string "#s(hash-table data (key (42 43)))"))))))

(deftestf 'hash-symbol-keys (yes)
  (el-expr `(gethash 'works (car (read-from-string "#s(hash-table data (works yes))")))))

;; Test special characters and escapes in hash context
(deftestf 'hash-string-key-value ("value")
  (el-expr `(gethash "key" (car (read-from-string "#s(hash-table test equal data (key\" value\"))")))))

;; Test that read-from-string returns correct position after hash syntax
(deftestf 'hash-position (27)
  (el-expr `(cdr (read-from-string "#s(hash-table data (a 1))"))))

(deftestf 'record-position (17)
  (el-expr `(cdr (read-from-string "#s(rec x y z) foo"))))
