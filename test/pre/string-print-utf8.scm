
(deftest print-utf8-2ch ("αβ")
  (el-expr `(let ((utf8-str "\"αβ\""))  ;; Just 2 Greek characters
              (print utf8-str))))

;;; Safe string test that handles expected errors

(let* ((ascii-str-unquoted "AxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxB") ;; 32 ASCII chars
       (ascii-str (format #f "\"~a\"" ascii-str-unquoted)))

  (deftestf 'print-ascii-32ch (ascii-str-unquoted)
    (el-expr `(print ,ascii-str)))

  (deftestf 'length-ascii-32ch (32)
    (el-expr `(print (length ,ascii-str))))

  ;; Test character access at boundaries safely
  (deftestf 'aref-ascii-32ch (65)
    (el-expr `(print (aref ,ascii-str 0))))

  (deftestf 'aref-ascii-32ch (66)
    (el-expr `(print (aref ,ascii-str 31))))

  ;; Test expected out-of-bounds access
  (deftestf 'aref-ascii-32ch ('args-out-of-range)
    (el-expr `(condition-case err
                (aref ,ascii-str 32)
                (error (print (car err))))))
  )

(let* ((utf8-str-unquoted "AxxxxxxxxxxxxxxyαβγδxxxxxxxB") ;; 16+4+8 = 28 UTF-8 chars
       (utf8-str (format #f "\"~a\"" utf8-str-unquoted)))

  (deftestf 'print-utf8-28ch (utf8-str-unquoted)
    (el-expr `(print ,utf8-str)))

  (deftestf 'length-utf8-28ch (28)
    (el-expr `(print (length ,utf8-str))))

  ;; access characters at different positions in the string (given as unicode codepoints)
  (deftest aref-utf8-28ch-0  (65) (el-expr `(print (aref ,utf8-str 0))))   ; A
  (deftest aref-utf8-28ch-15 (121) (el-expr `(print (aref ,utf8-str 15)))) ; y
  (deftest aref-utf8-28ch-16 (945) (el-expr `(print (aref ,utf8-str 16)))) ; α
  (deftest aref-utf8-28ch-17 (946) (el-expr `(print (aref ,utf8-str 17)))) ; β
  (deftest aref-utf8-28ch-28 (66) (el-expr `(print (aref ,utf8-str 27))))  ; B

  (deftestf 'aref-utf8-28ch-28 ('args-out-of-range)
    (el-expr `(condition-case err
                (aref ,utf8-str 28) ;; out of bounds, should fail
                (error (print (car err))))))

  )

;; Pure Greek String Test
(let* ((puregreek-unquoted "αβγδ") ;; 4 Greek chars = 8 bytes
       (puregreek (format #f "\"~a\"" puregreek-unquoted)))

  (deftestf 'print-puregreek (puregreek-unquoted)
    (el-expr `(print ,puregreek)))

  (deftestf 'length-puregreek (4)
    (el-expr `(print (length ,puregreek))))

  (deftest aref-puregreek-0 (945) (el-expr `(print (aref ,puregreek 0))))
  (deftest aref-puregreek-1 (946) (el-expr `(print (aref ,puregreek 1))))
  (deftest aref-puregreek-2 (947) (el-expr `(print (aref ,puregreek 2))))
  (deftest aref-puregreek-3 (948) (el-expr `(print (aref ,puregreek 3))))
  )
