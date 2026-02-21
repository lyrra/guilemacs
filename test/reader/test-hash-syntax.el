;;; test-hash-syntax.el --- Test reader #s(...) hash-table and record syntax

(test-begin "reader-hash-syntax")

;;; ============================================================
;;; read-from-string basic functionality
;;; ============================================================

;; Basic types
(test-eq "read-symbol" 'foo (car (read-from-string "foo")))
(test-equal "read-number" 42 (car (read-from-string "42")))
(test-equal "read-negative" -17 (car (read-from-string "-17")))
(test-equal "read-float" 3.14 (car (read-from-string "3.14")))
(test-equal "read-string" "hello" (car (read-from-string "\"hello\"")))
(test-eq "read-nil" nil (car (read-from-string "nil")))
(test-eq "read-t" t (car (read-from-string "t")))

;; Lists
(test-eq "read-empty-list" nil (car (read-from-string "()")))
(test-equal "read-simple-list" '(a b c) (car (read-from-string "(a b c)")))
(test-equal "read-nested-list" '((a b) (c d)) (car (read-from-string "((a b) (c d))")))
(test-equal "read-dotted-pair" '(a . b) (car (read-from-string "(a . b)")))

;; Vectors
(test-equal "read-vector" [1 2 3] (car (read-from-string "[1 2 3]")))
(test-equal "read-empty-vector" [] (car (read-from-string "[]")))

;; Quote syntax
(test-equal "read-quote" '(quote foo) (car (read-from-string "'foo")))
(test-equal "read-backquote" '(\` foo) (car (read-from-string "`foo")))

;;; ============================================================
;;; read-from-string position tracking
;;; ============================================================

(test-equal "read-pos-symbol" 3 (cdr (read-from-string "foo")))
(test-equal "read-pos-number" 5 (cdr (read-from-string "12345")))
(test-equal "read-pos-string" 4 (cdr (read-from-string "\"hi\"")))
(test-equal "read-pos-with-space" 5 (cdr (read-from-string "  foo")))
(test-equal "read-pos-list" 5 (cdr (read-from-string "(a b)")))

;;; ============================================================
;;; read-from-string with start/end parameters
;;; ============================================================

(test-eq "read-substr-middle" 'foo (car (read-from-string "xxxfooyyy" 3 6)))
(test-equal "read-substr-start" 123 (car (read-from-string "123abc" 0 3)))
(test-equal "read-substr-end" 456 (car (read-from-string "abc456" 3 6)))

;;; ============================================================
;;; #s(hash-table ...) syntax
;;; ============================================================

;; Basic hash-table reading
(let ((ht (car (read-from-string "#s(hash-table data (a 1 b 2))"))))
  (test-assert "hash-is-hash-table" (hash-table-p ht))
  (test-equal "hash-simple-a" 1 (gethash 'a ht))
  (test-equal "hash-simple-b" 2 (gethash 'b ht))
  (test-equal "hash-count-simple" 2 (hash-table-count ht)))

;; Empty hash-table
(let ((ht (car (read-from-string "#s(hash-table)"))))
  (test-assert "hash-empty-is-hash-table" (hash-table-p ht))
  (test-equal "hash-count-empty" 0 (hash-table-count ht)))

;; Hash-table with test parameter
;; NOTE: :test parameter not yet supported in Scheme reader - mark as expected fail
(let ((ht (car (read-from-string "#s(hash-table test equal data (\"x\" 10))"))))
  (test-assert "hash-with-test-is-hash-table" (hash-table-p ht))
  (test-expect-fail)
  (test-equal "hash-with-test-value" 10 (gethash "x" ht)))

;; Complex hash-table data
(let ((ht (car (read-from-string "#s(hash-table data (key (42 43)))"))))
  (test-equal "hash-nested-value" 42 (car (gethash 'key ht))))

(let ((ht (car (read-from-string "#s(hash-table data (works yes))"))))
  (test-eq "hash-symbol-keys" 'yes (gethash 'works ht)))

;; Position after hash-table
;; "#s(hash-table data (a 1))" is 25 chars (0-24), so position after is 25
(test-equal "hash-position" 25 (cdr (read-from-string "#s(hash-table data (a 1))")))

;;; ============================================================
;;; #s(record ...) syntax
;;; ============================================================

;; Records are represented as vectors with type in slot 0
(let ((rec (car (read-from-string "#s(my-record field1 field2)"))))
  (test-assert "record-is-vector" (vectorp rec))
  (test-eq "record-type-slot" 'my-record (aref rec 0))
  (test-eq "record-field1" 'field1 (aref rec 1))
  (test-eq "record-field2" 'field2 (aref rec 2))
  (test-equal "record-length" 3 (length rec)))

;; Position after record
(let ((result (read-from-string "#s(rec x y z) foo")))
  (test-equal "record-position" 13 (cdr result)))

;;; ============================================================
;;; read function with different stream types
;;; ============================================================

;; read from string
(test-eq "read-from-string-stream" 'hello (read "hello"))
(test-equal "read-number-from-string-stream" 42 (read "42"))
(test-equal "read-list-from-string-stream" '(a b c) (read "(a b c)"))

;; read from buffer
(with-temp-buffer
  (insert "symbol-in-buffer")
  (goto-char (point-min))
  (test-eq "read-from-buffer" 'symbol-in-buffer (read (current-buffer)))
  (test-equal "read-from-buffer-advances-point" 17 (point)))

(with-temp-buffer
  (insert "(list 1 2 3) extra")
  (goto-char (point-min))
  (test-equal "read-list-from-buffer" '(list 1 2 3) (read (current-buffer)))
  (test-equal "read-from-buffer-stops-after-sexp" 13 (point)))

;; read from marker
(with-temp-buffer
  (insert "first second third")
  (let ((m (copy-marker 7)))  ; points to "second"
    (test-eq "read-from-marker" 'second (read m))
    (test-equal "read-from-marker-advances" 13 (marker-position m))))

;; read-positioning-symbols (same as read for now)
(test-eq "read-positioning-symbols-string" 'test (read-positioning-symbols "test"))
(test-equal "read-positioning-symbols-list" '(a b) (read-positioning-symbols "(a b)"))

(test-end)
