;; this code that emits the test is as complex as any macro, just see the emitted code at test/pre/buffer-string.el
(let* ((bufcnt 0)
       (bufname (lambda ()
                  (set! bufcnt (+ 1 bufcnt))
                  (format #f "\"*temp-test-~a*\"" bufcnt)))
       (emit-test (lambda (name expect . body)
                    (let ((buffer-name (bufname)))
                      (deftestf name (expect)
                        (el-expr `(progn
                          ;; emulate with-temp-buffer (a defmacro not in the c-core)
                          (set-buffer (get-buffer-create ,buffer-name))
                          (let ((result (progn ,@body)))
                            (kill-buffer ,buffer-name)
                            (print result)))))))))

  ;; buffer-string on empty buffer should return empty string
  (emit-test 'buffer-string-empty ""
    '(erase-buffer)  ; Make sure it's empty
    '(buffer-string)))

  ;; Note, insert depends on elisp-code
  ;; Buffer-string after manual insert
  ;(emit-test 'buffer-insert-simple "hello"
  ;  '(erase-buffer)
  ;  '(insert "\"hello\"")
  ;  '(buffer-string))

  ;; Buffer size and boundaries after insert
  ;(emit-test 'buffer-boundaries-simple '(5 6 1 6)
  ;  '(erase-buffer)
  ;  '(insert "\"hello\"")
  ;  '(list (buffer-size) (point) (point-min) (point-max))))

#|
;; Test cases for buffer-string and insert-file-contents bug

(deftest buffer-string-empty ("")
  (el-expr `(progn
    (set-buffer (get-buffer-create "\"*temp-test*\""))
    (erase-buffer)  ; Make sure it's empty
      (buffer-string)))))

;; Test 2: buffer-substring on empty buffer should work
(deftest buffer-substring-empty ("")
  (el-expr `(progn
    (with-temp-buffer
      (buffer-substring (point-min) (point-max))))))

;; Test 3: Manual insert should update buffer metadata correctly
(deftest buffer-insert-metadata ((5 6 1 6 "hello"))
  (el-expr `(progn
    (with-temp-buffer
      (insert "hello")
      (list (buffer-size) (point) (point-min) (point-max) (buffer-string))))))

;; Test 4: File insertion should update buffer metadata correctly
(deftest buffer-file-insert-metadata ((8 1 1 9 "test123\\n"))
  (el-expr `(progn
    (let ((test-file "/tmp/prelude-buffer-test.txt"))
      (with-temp-file test-file
        (insert "test123\\n"))
      (with-temp-buffer
        (insert-file-contents test-file)
        (list (buffer-size) (point) (point-min) (point-max) (buffer-string)))))))

;; Test 5: Multiple inserts should accumulate correctly
(deftest buffer-multiple-inserts (("part1" "part1-part2"))
  (el-expr `(progn
    (with-temp-buffer
      (insert "part1")
      (let ((contents1 (buffer-string)))
        (insert "-part2")
        (let ((contents2 (buffer-string)))
          (list contents1 contents2)))))))

;; Test 6: Buffer state consistency after operations
(deftest buffer-state-consistency ((0 1 1 0 3 4 1 3))
  (el-expr `(progn
    (with-temp-buffer
      (let ((empty-size (buffer-size))
            (empty-point (point))
            (empty-min (point-min))
            (empty-max (- (point-max) (point-min))))  ; Convert to size for comparison
        (insert "xyz")
        (let ((filled-size (buffer-size))
              (filled-point (point))
              (filled-min (point-min))
              (filled-max (- (point-max) (point-min))))  ; Convert to size for comparison
          (list empty-size empty-point empty-min empty-max
                filled-size filled-point filled-min filled-max)))))))
|#
