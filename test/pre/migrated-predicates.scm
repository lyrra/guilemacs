;; Comprehensive tests for functions migrated from C to Guile
;; This covers null and characterp which were recently migrated

;; ===============================================
;; NULL FUNCTION TESTS (migrated from src/data.c)
;; ===============================================

;; Basic null tests
(deftest null-nil (t)
  (el-expr `(print (null nil))))

(deftest null-empty-list (t)
  (el-expr `(print (null '()))))

(deftest null-false-symbol (nil)
  (el-expr `(print (null 'false))))

(deftest null-zero (nil)
  (el-expr `(print (null 0))))

(deftest null-empty-string (nil)
  (el-expr `(let ((empty-str ""))
              (print (null empty-str)))))

(deftest null-t (nil)
  (el-expr `(print (null t))))

;; Test null with various data types
(deftest null-integer (nil)
  (el-expr `(print (null 42))))

(deftest null-negative-integer (nil)
  (el-expr `(print (null -42))))

(deftest null-float (nil)
  (el-expr `(print (null 3.14))))

(deftest null-negative-float (nil)
  (el-expr `(print (null -3.14))))

(deftest null-string (nil)
  (el-expr `(print (null "hello"))))

(deftest null-symbol (nil)
  (el-expr `(print (null 'symbol))))

(deftest null-cons (nil)
  (el-expr `(print (null '(a . b)))))

(deftest null-list (nil)
  (el-expr `(print (null '(1 2 3)))))

(deftest null-vector (nil)
  (el-expr `(print (null [1 2 3]))))

(deftest null-char (nil)
  (el-expr `(print (null ?a))))

;; Test null with special values
(deftest null-most-positive-fixnum (nil)
  (el-expr `(print (null most-positive-fixnum))))

(deftest null-most-negative-fixnum (nil)
  (el-expr `(print (null most-negative-fixnum))))

;; Test null with bignum
(let ((big (expt 2 70)))
  (deftest null-bignum (nil)
    (el-expr `(print (null ,big)))))

;; Test null with variable bindings
(deftest null-variable-nil (t)
  (el-expr `(let ((x nil))
              (print (null x)))))

(deftest null-variable-non-nil (nil)
  (el-expr `(let ((x 'something))
              (print (null x)))))

;; Test null with nested expressions
(deftest null-car-nil-list (t)
  (el-expr `(print (null (car '(nil))))))

(deftest null-cdr-single-list (t)
  (el-expr `(print (null (cdr '(only))))))

;; ===================================================
;; CHARACTERP FUNCTION TESTS (migrated from src/character.c)
;; ===================================================

;; Basic character tests
(deftest characterp-char-literal (t)
  (el-expr `(print (characterp ?a))))

(deftest characterp-char-literal-A (t)
  (el-expr `(print (characterp ?A))))

(deftest characterp-space-char (t)
  (el-expr `(print (characterp ?\s))))

(deftest characterp-newline-char (t)
  (el-expr `(print (characterp ?\n))))

(deftest characterp-tab-char (t)
  (el-expr `(print (characterp ?\t))))

;; Test characterp with integers (character codes)
(deftest characterp-ascii-A (t)
  (el-expr `(print (characterp 65))))    ; ASCII 'A'

(deftest characterp-ascii-a (t)
  (el-expr `(print (characterp 97))))    ; ASCII 'a'

(deftest characterp-ascii-0 (t)
  (el-expr `(print (characterp 48))))    ; ASCII '0'

(deftest characterp-ascii-space (t)
  (el-expr `(print (characterp 32))))    ; ASCII space

;; Test characterp with Unicode characters
(deftest characterp-unicode-alpha (t)
  (el-expr `(print (characterp #x3b1)))) ; Greek alpha α

(deftest characterp-unicode-arrow (t)
  (el-expr `(print (characterp #x2190)))) ; Left arrow ←

(deftest characterp-unicode-emoji (t)
  (el-expr `(print (characterp #x270a)))) ; Raised fist ✊

;; Test characterp boundary values
(deftest characterp-zero (t)
  (el-expr `(print (characterp 0))))

(deftest characterp-max-char (t)
  (el-expr `(print (characterp (max-char)))))

(deftest characterp-max-unicode (t)
  (el-expr `(print (characterp 1114111)))) ; Max Unicode code point

;; Test characterp with invalid character codes
(deftest characterp-negative (nil)
  (el-expr `(print (characterp -1))))

(deftest characterp-too-large (nil)
  (el-expr `(print (characterp 4194303)))) ; Above max-char

(deftest characterp-way-too-large (nil)
  (el-expr `(print (characterp 10000000))))

;; Test characterp with non-numeric types
(deftest characterp-nil (nil)
  (el-expr `(print (characterp nil))))

(deftest characterp-t (nil)
  (el-expr `(print (characterp t))))

(deftest characterp-string (nil)
  (el-expr `(print (characterp "A"))))

(deftest characterp-empty-string (nil)
  (el-expr `(print (characterp ""))))

(deftest characterp-symbol (nil)
  (el-expr `(print (characterp 'symbol))))

(deftest characterp-list (nil)
  (el-expr `(print (characterp '(1 2 3)))))

(deftest characterp-cons (nil)
  (el-expr `(print (characterp '(a . b)))))

(deftest characterp-vector (nil)
  (el-expr `(print (characterp [1 2 3]))))

(deftest characterp-float (nil)
  (el-expr `(print (characterp 65.0))))

(deftest characterp-float-int-value (nil)
  (el-expr `(print (characterp 65.5))))

;; Test characterp with bignum
(let ((big (expt 2 70)))
  (deftest characterp-bignum (nil)
    (el-expr `(print (characterp ,big)))))

;; Test characterp with special fixnum values
(deftest characterp-most-positive-fixnum (nil)
  (el-expr `(print (characterp most-positive-fixnum))))

(deftest characterp-most-negative-fixnum (nil)
  (el-expr `(print (characterp most-negative-fixnum))))

;; Test characterp with variable bindings
(deftest characterp-variable-char (t)
  (el-expr `(let ((c ?z))
              (print (characterp c)))))

(deftest characterp-variable-int (t)
  (el-expr `(let ((c 122))  ; ASCII 'z'
              (print (characterp c)))))

(deftest characterp-variable-non-char (nil)
  (el-expr `(let ((c "not-char"))
              (print (characterp c)))))

;; Test characterp with expressions
(deftest characterp-plus-chars (t)
  (el-expr `(print (characterp (+ ?a 1))))) ; ?a + 1 = ?b

(deftest characterp-char-arithmetic (t)
  (el-expr `(print (characterp (- ?z ?a))))) ; Should be a valid char code

;; Test edge cases for characterp
(deftest characterp-control-chars (t)
  (el-expr `(print (and (characterp 1)   ; Control-A
                        (characterp 7)   ; Bell
                        (characterp 127))))) ; DEL

;; Test characterp with high Unicode
(deftest characterp-high-unicode-plane (t)
  (el-expr `(print (characterp #x1F600)))) ; Emoji if supported

;; Comprehensive range test for characterp - valid codes
(deftest characterp-code-0 (t)
  (el-expr `(print (characterp 0))))

(deftest characterp-code-1 (t)
  (el-expr `(print (characterp 1))))

(deftest characterp-code-32 (t)
  (el-expr `(print (characterp 32))))

(deftest characterp-code-65 (t)
  (el-expr `(print (characterp 65))))

(deftest characterp-code-97 (t)
  (el-expr `(print (characterp 97))))

(deftest characterp-code-127 (t)
  (el-expr `(print (characterp 127))))

(deftest characterp-code-255 (t)
  (el-expr `(print (characterp 255))))

(deftest characterp-code-256 (t)
  (el-expr `(print (characterp 256))))

(deftest characterp-code-1023 (t)
  (el-expr `(print (characterp 1023))))

(deftest characterp-code-1024 (t)
  (el-expr `(print (characterp 1024))))

(deftest characterp-code-65535 (t)
  (el-expr `(print (characterp 65535))))

(deftest characterp-code-65536 (t)
  (el-expr `(print (characterp 65536))))

(deftest characterp-code-1114111 (t)
  (el-expr `(print (characterp 1114111))))

;; Invalid character codes
(deftest characterp-code-1114112 (nil)
  (el-expr `(print (characterp 1114112))))

(deftest characterp-code-negative (nil)
  (el-expr `(print (characterp -1))))

;; =======================================================
;; INTEGRATION TESTS - Testing interactions between functions
;; =======================================================

;; Test null and characterp together
(deftest null-characterp-interaction (nil)
  (el-expr `(print (null (characterp ?a)))))

(deftest characterp-null-interaction (nil)
  (el-expr `(print (characterp (null nil)))))

;; Test with conditional expressions
(deftest conditional-null (t)
  (el-expr `(print (if (null nil) t nil))))

(deftest conditional-characterp (t)
  (el-expr `(print (if (characterp ?a) t nil))))

;; Test with logical combinations
(deftest logical-and-predicates (nil)
  (el-expr `(print (and (null nil) (characterp "not-char")))))

(deftest logical-or-predicates (t)
  (el-expr `(print (or (null 'something) (characterp 65)))))

;; Test predicate negation
(deftest not-null-nil (nil)
  (el-expr `(print (not (null nil)))))

(deftest not-null-something (t)
  (el-expr `(print (not (null 'something)))))

(deftest not-characterp-char (nil)
  (el-expr `(print (not (characterp ?a)))))

(deftest not-characterp-string (t)
  (el-expr `(print (not (characterp "a")))))