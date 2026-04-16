(let-syntax
  ((test
    (syntax-rules ()
      ((_ name e res)
       (deftest name (res)
         (elfmt `(print (recordp e))))))))
  ;; Basic recordp tests
  (test recordp-nil nil nil)
  (test recordp-symbol 's nil)
  (test recordp-vector (raw "[]") nil)
  (test recordp-list '() nil)
  (test recordp-string "" nil)
  (test recordp-number 0 nil)
  (test recordp-hash-table (make-hash-table) nil)

  (test recordp-empty (record 's0) t)
  (test recordp-simple (record 's1 0) t)
  (test recordp-bazaar (record 'bazaar nil t 0 0.1 "" (record 's2) (raw "[]") () (make-hash-table)) t)
  )
;; length
(deftest record-record-length-1 (1)
  (elfmt `(print (record-length (record 's3)))))
(deftest record-record-length-2 (2)
  (elfmt `(print (record-length (record 's3 0)))))
(deftest record-length-1 (1)
  (elfmt `(print (length (record 's4)))))
(deftest record-length-2 (2)
  (elfmt `(print (length (record 's5 0)))))
;; access
(deftest record-aref-0 (s6)
  (elfmt `(print (aref (record 's6) 0))))
(deftest record-aref-1 (0)
  (elfmt `(print (aref (record 's7 0) 1))))

;; aset on record must return the set value (not #<unspecified>)
;; This was a bug where elisp-record-set! returned unspecified from vector-set!
(deftest record-aset-returns-value (42)
  (elfmt `(print (aset (record 's8 0) 1 42))))
(deftest record-aset-returns-value-symbol (hello)
  (elfmt `(print (aset (record 's9 nil) 1 'hello))))
(deftest record-aset-returns-value-string ("test")
  (elfmt `(print (aset (record 's10 nil) 1 "test"))))
