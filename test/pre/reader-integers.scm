;;; Test file for Guile reader integer integration
;;; This tests that integers are read correctly using Guile's reader

(let-syntax ((emit-test
              (syntax-rules ()
                ((_ name num e)
                 (deftestf 'name (e)
                   (el-expr `(progn (prin1 ,num) (terpri))))))))

  ;; Decimal integers

  (emit-test dec-42   "42" 42)
  (emit-test dec--42  "-42" -42)
  (emit-test dec-0    "0" 0)
  (emit-test dec-positive-explicit "+42" 42)

  ;; Hexadecimal integers
  (emit-test hex-1f       "#x1F" 31)
  (emit-test hex-deadbeef "#xDEADBEEF" 3735928559)
  (emit-test hex-ffffffff "#xffffffff" 4294967295)

  ;; Octal integers
  (emit-test oct-777 "#o777" 511)
  (emit-test oct-123 "#o123" 83)

  ;; Binary integers
  (emit-test bin-1010     "#b1010" 10)
  (emit-test bin-11111111 "#b11111111" 255)

  ;; Radix-N integers
  ;(emit-test radix-36-1z   "#36r1z" 71)   ; base-36
  ;(emit-test radix-10-99   "#10r99" 99)   ; base-10
  ;(emit-test radix-2-1111  "#2r1111" 15)  ; base-2 (same as #b1111)

  ;; Large integers
  (emit-test large-int "1234567890123456789012345678901234567890" 1234567890123456789012345678901234567890)

  ;; Edge cases
  (emit-test hex-zero "#x0" 0)
  (emit-test oct-zero "#o0" 0)
  (emit-test bin-zero "#b0" 0)

  ;(emit-test negative-hex "-#x1F" 0)
  ;(emit-test negative-oct "-#o777" 0)
  ;(emit-test negative-bin "-#b1010" 0)

  ;; More radix tests
  ;(emit-test radix-16-ff "#16rFF" 0)    ; base-16 equivalent to #xFF
  ;(emit-test radix-8-377 "#8r377" 0)    ; base-8 equivalent to #o377
  ;(emit-test radix-35-zz "#35rZZ" 0)    ; base-35 maximum digits

)
