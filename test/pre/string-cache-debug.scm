(deftest string-cache-debug (ok)
  (el-expr `(progn
    ;; Test string cache behavior with UTF-8 strings
    ;; The cache variables might be contaminated from previous operations
    (let ((test-string "\"λ\""))
      ;; Clear any potential cache contamination by using a different string first
      (let ((dummy-result (string-match "\"a\"" "\"abc\"")))
        (when (not (equal 0 dummy-result))
          (print "\"wrong dummy string-match result\"")
          (print dummy-result)))

      ;; Now test our UTF-8 string
      (let ((result (string-match "\"λ\"" test-string)))
        (cond
          ((equal result 0)
           (print 'ok))
          (t
           (print 'fail))))))))

(deftest string-ascii-vs-utf8 (ok)
  (el-expr `(let ((pass t))
    ;; Compare ASCII vs UTF-8 string behavior

    ;; Test ASCII string first
    (let ((ascii-string "\"a\""))
      (when (not (equal 1 (length ascii-string)))
        (setq pass nil)
        (message "\"wrong ASCII length: %d\"" (length ascii-string)))
      (when (not (equal 1 (string-bytes ascii-string)))
        (setq pass nil)
        (message "\"wrong ASCII bytes: %d\"" (string-bytes ascii-string)))
      (let ((result (string-match "\"a\"" ascii-string)))
        (when (not (equal 0 result))
          (setq pass nil)
          (message "\"wrong ASCII string-match result: %s\"" result))))

    ;; Test UTF-8 string second
    (let ((utf8-string "\"λ\""))
      (when (not (equal 1 (length utf8-string)))
        (setq pass nil)
        (message "\"wrong UTF-8 length: %d\"" (length utf8-string)))
      (when (not (equal 2 (string-bytes utf8-string)))
        (setq pass nil)
        (message "\"wrong UTF-8 bytes: %d\"" (string-bytes utf8-string)))
      (let ((result (string-match "\"λ\"" utf8-string)))
        (when (not (equal 0 result))
          (setq pass nil)
          (message "\"wrong UTF-8 string-match result: %s\"" result))))
    (if pass (print 'ok) (print 'fail)))))

(deftest string-multibyte-boundaries (ok)
  (el-expr `(let ((pass t))
    ;; Test various UTF-8 character boundaries
    ;; Test single UTF-8 char
    (let ((single-utf8 "\"λ\""))
      (when (not (and (equal 1 (length single-utf8))
                      (equal 2 (string-bytes single-utf8))))
        (setq pass nil)
        (message "\"wrong Single UTF-8: %s (len=%d, bytes=%d)\"" single-utf8 (length single-utf8) (string-bytes single-utf8))))

    ;; Test mixed ASCII + UTF-8
    (let ((mixed-string "\"aλb\""))
      (when (not (and (equal 3 (length mixed-string))
                      (equal 4 (string-bytes mixed-string))))
        (setq pass nil)
        (message "\"Mixed string: %s (len=%d, bytes=%d)\"" mixed-string (length mixed-string) (string-bytes mixed-string)))
      (let ((result (string-match "\"λ\"" mixed-string)))
        (when (not (equal 1 result))
          (setq pass nil)
          (message "\"Mixed string-match result: %s\\n\"" result))))

    ;; Test multiple UTF-8 chars
    (let ((multi-utf8 "\"λμν\""))
      (when (not (and (equal 3 (length multi-utf8))
                      (equal 6 (string-bytes multi-utf8))))
        (setq pass nil)
        (message "\"wrong: Multi UTF-8: %s (len=%d, bytes=%d)\"" multi-utf8 (length multi-utf8) (string-bytes multi-utf8))))
    (if pass
        (print 'ok) (print 'fail)))))
