;;; test-casefiddle.el --- Test case conversion with emacs-string wrappers

;; These tests verify that upcase, downcase, capitalize, and upcase-initials
;; work correctly with both plain strings and emacs-string wrappers
;; (strings with text properties).

(test-begin "casefiddle")

;; Test 1: upcase with plain string
(test-equal "upcase/plain-string" "HELLO" (upcase "hello"))
(test-equal "upcase/mixed-case" "HELLO WORLD" (upcase "Hello World"))
(test-equal "upcase/already-upper" "HELLO" (upcase "HELLO"))
(test-equal "upcase/empty-string" "" (upcase ""))

;; Test 2: downcase with plain string
(test-equal "downcase/plain-string" "hello" (downcase "HELLO"))
(test-equal "downcase/mixed-case" "hello world" (downcase "Hello World"))
(test-equal "downcase/already-lower" "hello" (downcase "hello"))
(test-equal "downcase/empty-string" "" (downcase ""))

;; Test 3: capitalize with plain string
(test-equal "capitalize/plain-string" "Hello" (capitalize "hello"))
(test-equal "capitalize/all-upper" "Hello" (capitalize "HELLO"))
(test-equal "capitalize/multiple-words" "Hello World" (capitalize "hello world"))

;; Test 4: upcase-initials with plain string
;; Note: Current implementation uses Guile's titlecase which lowercases the rest,
;; unlike vanilla Emacs which preserves the rest. This is a known difference.
(test-equal "upcase-initials/plain-string" "Hello" (upcase-initials "hello"))
(test-equal "upcase-initials/multiple-words" "Hello World" (upcase-initials "hello world"))
;; In vanilla Emacs this would be "HELLO", but Guile titlecase makes it "Hello"
(test-equal "upcase-initials/titlecase-behavior" "Hello" (upcase-initials "hELLO"))

;; Test 5: upcase with character
(test-equal "upcase/character-a" ?A (upcase ?a))
(test-equal "upcase/character-z" ?Z (upcase ?z))
(test-equal "upcase/character-already-upper" ?A (upcase ?A))

;; Test 6: downcase with character
(test-equal "downcase/character-A" ?a (downcase ?A))
(test-equal "downcase/character-Z" ?z (downcase ?Z))
(test-equal "downcase/character-already-lower" ?a (downcase ?a))

;; Test 7: upcase with emacs-string wrapper (propertized string)
(let ((str (propertize "hello" 'face 'bold)))
  (test-equal "upcase/propertized-string" "HELLO" (upcase str)))

;; Test 8: downcase with emacs-string wrapper
(let ((str (propertize "HELLO" 'face 'bold)))
  (test-equal "downcase/propertized-string" "hello" (downcase str)))

;; Test 9: capitalize with emacs-string wrapper
(let ((str (propertize "hello world" 'face 'bold)))
  (test-equal "capitalize/propertized-string" "Hello World" (capitalize str)))

;; Test 10: upcase-initials with emacs-string wrapper
(let ((str (propertize "hello world" 'face 'bold)))
  (test-equal "upcase-initials/propertized-string" "Hello World" (upcase-initials str)))

;; Test 11: upcase with substring of propertized string
;; This tests that substring returns an emacs-string and upcase handles it
(let* ((str (propertize "hello world" 'face 'bold))
       (sub (substring str 0 5)))
  (test-equal "upcase/substring-of-propertized" "HELLO" (upcase sub)))

;; Test 12: downcase with buffer-substring (which may return emacs-string)
(with-temp-buffer
  (insert "HELLO")
  (put-text-property 1 6 'face 'bold)
  (let ((str (buffer-substring 1 6)))
    (test-equal "downcase/buffer-substring" "hello" (downcase str))))

;; Test 13: upcase with short propertized strings (like org-mode code block keywords)
(let ((str (propertize "SRC" 'face 'org-block)))
  (test-equal "upcase/short-propertized-src" "SRC" (upcase str)))

(let ((str (propertize "src" 'face 'org-block)))
  (test-equal "upcase/short-propertized-src-lower" "SRC" (upcase str)))

;; Test 14: Unicode strings (if locale supports)
(test-equal "upcase/unicode-basic" "ABC" (upcase "abc"))
(test-equal "downcase/unicode-basic" "abc" (downcase "ABC"))

;; Test 15: Numbers and special chars unchanged
(test-equal "upcase/numbers-unchanged" "ABC123" (upcase "abc123"))
(test-equal "downcase/numbers-unchanged" "abc123" (downcase "ABC123"))
(test-equal "upcase/special-chars" "HELLO!" (upcase "hello!"))

(test-end)
