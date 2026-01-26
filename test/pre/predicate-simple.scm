;; symbolp predicate tests
;; Returns t if OBJECT is a symbol (including t and nil)

(for-each (lambda (test-case)
            (match test-case
              ((name input expected)
               (deftestf name (expected)
                 (el-expr `(print (symbolp ,input)))))))
  '(
    ;; t and nil are symbols in Elisp
    (symbolp-t t t)
    (symbolp-nil nil t)

    ;; Regular symbols
    (symbolp-foo 'foo t)
    (symbolp-bar 'bar t)

    ;; Non-symbols should return nil
    (symbolp-zero 0 nil)
    (symbolp-positive 42 nil)
    (symbolp-negative -1 nil)
    (symbolp-float 3.14 nil)
    ))
