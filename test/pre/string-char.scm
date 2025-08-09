
;;; Test char-to-string and string-to-char

(let* ((emit-test (lambda (name codepoint char)
                    (deftestf name (char)
                      (el-expr `(let ((n ,codepoint))
                                  (print (char-to-string n))))))))
  ; some ascii (1-byte utf-8)
  (emit-test 'test-char-to-string-A 65 "A")
  (emit-test 'test-char-to-string-Z 90 "Z")
  (emit-test 'test-char-to-string-0 48 "0")
  ; 2 byte utf-8
  (emit-test 'test-char-to-string-alpha #x3b1 "α")
  ; 3 byte utf-8
  (emit-test 'test-char-to-string-leftarrow #x2190 "←")
  (emit-test 'test-char-to-string-raisedfist #x270a "✊")
  ; 4 byte utf-8
  ;(emit-test 'test-char-to-string-dropofblood #x1fa78 "喝") ; drop of blood
  )

; test roundtrip: string -> string-to-char
(let* ((emit-test (lambda (name codepoint)
                    (deftestf name (codepoint)
                      (el-expr `(let ((n ,codepoint))
                                  (let ((s (string n)))
                                    (print (string-to-char s)))))))))
  ; some ascii (1-byte utf-8)
  (emit-test 'test-string-to-char-A 65)
  (emit-test 'test-string-to-char-Z 90)
  (emit-test 'test-string-to-char-0 48)
  ; 2 byte utf-8
  (emit-test 'test-string-to-char-alpha #x3b1)
  ; 3 byte utf-8
  (emit-test 'test-string-to-char-leftarrow #x2190)
  (emit-test 'test-string-to-char-raisedfist #x270a) ; raised fist
  ; 4 byte utf-8
  (emit-test 'test-string-to-char-dropofblood #x1fa78) ; drop of blood
  )
