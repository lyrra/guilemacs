(deftest xfail-condition-case-void-function (nilt)
  (el-expr `(progn
    (condition-case err
      (signal 'void-function nil)
      (void-function nil)
      (error (princ nil)))
    (princ t))))
