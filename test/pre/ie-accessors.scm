;; Field accessors for the ie-smob (struct input_event handle).
;;
;; ie-smobs cannot yet be constructed from elisp (ie_wrap is unexposed),
;; so these tests only verify DEFUN registration and the CHECK_IE guard
;; that every accessor inherits via the NULL/type-check mandate.

(deftest ie-kind-fboundp (t)
  (el-expr `(print (fboundp '--ie-kind))))

(deftest ie-kind-subrp (t)
  (el-expr `(print (subrp (symbol-function '--ie-kind)))))

(deftest ie-kind-rejects-non-smob (wrong-type-argument)
  (el-expr `(print (condition-case err
                       (progn (--ie-kind nil) 'no-signal)
                     (error (car err))))))
