;; number-or-marker-p predicate tests
;; Tests that number-or-marker-p correctly handles markers
;;
;; Bug: elisp-number-or-marker-p only checks (number? object),
;; not markers. When used via direct-module-ref, markers return nil.

(deftest number-or-marker-p-with-marker (ok)
  (el-expr `(let ((buf (get-buffer-create "\" *test*\"")))
              (set-buffer buf)
              (erase-buffer)
              (insert "\"hello world\"")
              (let ((m (point-marker)))
                (let ((val (if (number-or-marker-p m)
                               m
                             "\"not-a-number\"")))
                  (goto-char val)
                  (kill-buffer buf)
                  (print 'ok))))))
