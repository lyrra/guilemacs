;; stringp predicate tests
;; Returns t if OBJECT is a string

;; Test stringp with various inputs
(for-each (lambda (test-case)
            (match test-case
              ((name input expected)
               (deftestf name (expected)
                 (el-expr `(print (stringp ,input)))))))
  '(
    ;; Strings - should return t
;   (stringp-empty-string "\"\"" t)
    (stringp-single-char "\"a\"" t)
    (stringp-word "\"hello\"" t)
    (stringp-with-spaces "\"hello world\"" t)
    (stringp-with-newline "\"hello\\nworld\"" t)
    (stringp-with-tab "\"hello\\tworld\"" t)
    (stringp-numeric-string "\"123\"" t)
;   (stringp-unicode "\"hello\\u00e9\"" t)  ; hello + e-acute

    ;; Numbers - should return nil
;   (stringp-zero 0 nil)
;   (stringp-positive-int 42 nil)
;   (stringp-negative-int -42 nil)
;   (stringp-float 3.14 nil)
;   (stringp-float-zero 0.0 nil)

    ;; Symbols - should return nil
;   (stringp-nil nil nil)
;   (stringp-t t nil)
;   (stringp-symbol 'foo nil)
;   (stringp-keyword :keyword nil)

    ;; Other types - should return nil
;   (stringp-cons '(1 . 2) nil)
;   (stringp-list '(1 2 3) nil)
;   (stringp-vector "[1 2 3]" nil)
;   (stringp-empty-list '() nil)
    ))
