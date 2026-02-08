(deftest condition-case-void-function (t)
  (el-expr `(progn
    (condition-case err
      (signal 'void-function nil)
      (void-function nil)
      (error (princ nil)))
    (princ t))))
