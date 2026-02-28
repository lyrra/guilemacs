;; Test cases for string operations migrated from C to pure Guile
;; Tests for case-insensitive operations and new string utilities

;; Test string-equal-ignore-case function
(deftest string-equal-ignore-case-same (t)
  (elfmt `(print (string-equal-ignore-case "hello" "HELLO"))))

(deftest string-equal-ignore-case-different (nil)
  (elfmt `(print (string-equal-ignore-case "hello" "world"))))

(deftest string-equal-ignore-case-symbols (t)
  (elfmt `(print (string-equal-ignore-case 'hello 'HELLO))))

(deftest string-equal-ignore-case-mixed (t)
  (elfmt `(print (string-equal-ignore-case "Test" 'test))))

;; Test string-lessp-ignore-case function
(deftest string-lessp-ignore-case-true (t)
  (elfmt `(print (string-lessp-ignore-case "apple" "BANANA"))))

(deftest string-lessp-ignore-case-false (nil)
  (elfmt `(print (string-lessp-ignore-case "zebra" "APPLE"))))

(deftest string-lessp-ignore-case-equal (nil)
  (elfmt `(print (string-lessp-ignore-case "test" "TEST"))))

;; Test string-greaterp function
(deftest string-greaterp-true (t)
  (elfmt `(print (string-greaterp "zebra" "apple"))))

(deftest string-greaterp-false (nil)
  (elfmt `(print (string-greaterp "apple" "zebra"))))

(deftest string-greaterp-equal-same (nil)
  (elfmt `(print (string-greaterp "test" "test"))))
(deftest string-greaterp-equal-lt (nil)
  (elfmt `(print (string-greaterp "a" "b"))))
(deftest string-greaterp-equal-gt (t)
  (elfmt `(print (string-greaterp "b" "a"))))
(deftest string-greaterp-equal-gt-empty (t)
  (elfmt `(print (string-greaterp "b" ""))))
(deftest string-greaterp-equal-lt-empty (nil)
  (elfmt `(print (string-greaterp "" "a"))))

;;; Test string-greaterp-ignore-case function
;(deftest string-greaterp-ignore-case-true (t)
;  (elfmt `(print (string-greaterp-ignore-case "ZEBRA" "apple"))))

;(deftest string-greaterp-ignore-case-false (nil)
;  (elfmt `(print (string-greaterp-ignore-case "APPLE" "zebra"))))

;; Test string-prefix-p function
(deftest string-prefix-p-true (t)
  (elfmt `(print (string-prefix-p "hello" "hello world"))))

(deftest string-prefix-p-false (nil)
  (elfmt `(print (string-prefix-p "world" "hello world"))))

(deftest string-prefix-p-empty (t)
  (elfmt `(print (string-prefix-p "" "hello"))))

(deftest string-prefix-p-ignore-case-true (t)
  (elfmt `(print (string-prefix-p "HELLO" "hello world" t))))

(deftest string-prefix-p-ignore-case-false (nil)
  (elfmt `(print (string-prefix-p "HELLO" "hello world" nil))))

;; Test string-suffix-p function
(deftest string-suffix-p-true (t)
  (elfmt `(print (string-suffix-p "world" "hello world"))))

(deftest string-suffix-p-false (nil)
  (elfmt `(print (string-suffix-p "hello" "hello world"))))

(deftest string-suffix-p-empty (t)
  (elfmt `(print (string-suffix-p "" "hello"))))

; lisp/subr-x
;(deftest string-suffix-p-ignore-case-true (t)
;  (elfmt `(print (string-suffix-p "WORLD" "hello world" t))))
;(deftest string-blank-p-empty (t)
;  (elfmt `(print (string-blank-p ""))))
;(deftest string-blank-p-spaces (t)
;  (elfmt `(print (string-blank-p "   "))))
;(deftest string-blank-p-tabs (t)
;  (elfmt `(print (string-blank-p "\t\t"))))
;(deftest string-blank-p-mixed-whitespace (t)
;  (elfmt `(print (string-blank-p " \t\n "))))
;(deftest string-blank-p-not-blank (nil)
;  (elfmt `(print (string-blank-p " hello "))))
;(deftest string-blank-p-single-char (nil)
;  (elfmt `(print (string-blank-p "a"))))
