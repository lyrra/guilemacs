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

; FIX-20260212-guilemacs, what is the status with stringp and text-properties?
'(deftest stringp-propertized-string (ok)
  (el-expr `(if (stringp (propertize "\"hello\"" 'face 'bold))
                (print 'ok)
              (print 'fail))))

'(deftest stringp-buffer-substring-with-props (ok)
  (el-expr `(let ((buf (get-buffer-create "\" *stringp-test*\"")))
              (set-buffer buf)
              (erase-buffer)
              (insert (propertize "\"hello\"" 'face 'bold))
              (let ((s (buffer-substring (point-min) (point-max))))
                (kill-buffer buf)
                (if (stringp s)
                    (print 'ok)
                  (print 'fail))))))

'(deftest stringp-buffer-string-with-props (ok)
  (el-expr `(let ((buf (get-buffer-create "\" *stringp-test2*\"")))
              (set-buffer buf)
              (erase-buffer)
              (insert (propertize "\"world\"" 'custom-prop 'value))
              (let ((s (buffer-string)))
                (kill-buffer buf)
                (if (stringp s)
                    (print 'ok)
                  (print 'fail))))))

;; Test that triggers "Wrong type argument: stringp, <number>" when bug exists.
;; This simulates the eshell error where stringp returning nil causes code to
;; fall through and pass a buffer position to string-match.
'(deftest stringp-trigger-wrong-type-error (ok)
  (el-expr `(let ((buf (get-buffer-create "\" *trigger-test*\"")))
              (set-buffer buf)
              (erase-buffer)
              (insert "\"prefix text\"")
              (let ((input (propertize "\"echo\"" 'face 'bold)))
                (let ((cmd (if (stringp input)
                               input
                             (point))))
                  (string-match "\"echo\"" cmd)
                  (kill-buffer buf)
                  (print 'ok))))))
