(deftest buffer-string-codec (ok)
  (el-expr `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name "\" \"") nil))
    (insert "\"‘\"")
    (buffer-string)
    (print 'ok))))

(deftest buffer-string-point ((10 1 10 9))
  (el-expr `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name "\" \"") nil))
    (insert "\" ‘ ’ “ ” \"")
    (print (list (point) (point-min) (point-max) (buffer-size))))))

(deftest buffer-string-misc ((19 19 19 1 20 19))
  (el-expr `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name "\" \"") nil))
    (insert "\" ‘ ’ “ ” \\n ‘ ’ “ ” \"")
    (let ((n (re-search-backward "\"[^\\n]\"" nil t)))
      (delete-region (point) (- (point-max) 1))
      (let ((s (length (buffer-string))))
        (print (list n s (point) (point-min) (point-max) (buffer-size))))))))

(deftest buffer-goto (q2525nil13225)
  (el-expr `(progn
    (set-buffer (get-buffer-create (generate-new-buffer-name "\" \"") nil))
    (insert "\" λλλλλλ‘ ’ “ ” λλλλλλλλ \"")
    (print 'q)
    (print (point))
    (goto-char (point-max))
    (print (point))
    (print (char-after 0))
    (goto-char (point-min))
    (print (point))
    (print (char-after))
    (print (point-max)))))
