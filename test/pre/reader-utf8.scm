
; just to show how guile run-tests script converts a test case to emacs, this test...
(deftest reader-utf8-1 (ok)
  (el-expr `(let (("λ" 1)) ;; use lambda symbol as variable name
              (if (equal 1 "λ")
                (print 'ok)
                (print 'fail)))))

; ...is the same as this test:
(deftest reader-utf8-2 (ok)
  (el-expr `(let ((⌨ 1)) ;; again, use a keyboard symbol as variable name
              (if (equal 1 ⌨)
                (print 'ok)
                (print 'fail)))))
