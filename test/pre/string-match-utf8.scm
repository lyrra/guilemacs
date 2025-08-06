
(deftest string-match-utf8 (ok)
  (el-expr `(let ((pass t))
    ;; Test the C function string-match
    (let ((test-string "\"λ\"")) ;; this string should return character position 0 for byte position 0
      (when (not (equal 1 (length test-string)))
        (setq pass nil)
        (message "\"string-length (SCHARS): %d\"" (length test-string)))  ; Should be 1 char
      ;; This should call string_byte_to_char, via:
      ;;   string-match -> regex engine -> syntax table -> string_byte_to_char
      (let ((result (string-match "\"λ\"" test-string)))
        (cond
          ((and pass (equal result 0))
           (print 'ok))
          (t
           (print 'fail))))))))
