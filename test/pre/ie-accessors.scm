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

(deftest ie-code-fboundp (t)
  (el-expr `(print (fboundp '--ie-code))))

(deftest ie-code-subrp (t)
  (el-expr `(print (subrp (symbol-function '--ie-code)))))

(deftest ie-code-rejects-non-smob (wrong-type-argument)
  (el-expr `(print (condition-case err
                       (progn (--ie-code nil) 'no-signal)
                     (error (car err))))))

(deftest ie-modifiers-fboundp (t)
  (el-expr `(print (fboundp '--ie-modifiers))))

(deftest ie-modifiers-subrp (t)
  (el-expr `(print (subrp (symbol-function '--ie-modifiers)))))

(deftest ie-modifiers-rejects-non-smob (wrong-type-argument)
  (el-expr `(print (condition-case err
                       (progn (--ie-modifiers nil) 'no-signal)
                     (error (car err))))))

(deftest ie-part-fboundp (t)
  (el-expr `(print (fboundp '--ie-part))))

(deftest ie-part-subrp (t)
  (el-expr `(print (subrp (symbol-function '--ie-part)))))

(deftest ie-part-rejects-non-smob (wrong-type-argument)
  (el-expr `(print (condition-case err
                       (progn (--ie-part nil) 'no-signal)
                     (error (car err))))))

(deftest ie-x-fboundp (t)
  (el-expr `(print (fboundp '--ie-x))))

(deftest ie-x-subrp (t)
  (el-expr `(print (subrp (symbol-function '--ie-x)))))

(deftest ie-x-rejects-non-smob (wrong-type-argument)
  (el-expr `(print (condition-case err
                       (progn (--ie-x nil) 'no-signal)
                     (error (car err))))))

(deftest ie-y-fboundp (t)
  (el-expr `(print (fboundp '--ie-y))))

(deftest ie-y-subrp (t)
  (el-expr `(print (subrp (symbol-function '--ie-y)))))

(deftest ie-y-rejects-non-smob (wrong-type-argument)
  (el-expr `(print (condition-case err
                       (progn (--ie-y nil) 'no-signal)
                     (error (car err))))))

(deftest ie-frame-or-window-fboundp (t)
  (el-expr `(print (fboundp '--ie-frame-or-window))))

(deftest ie-frame-or-window-subrp (t)
  (el-expr `(print (subrp (symbol-function '--ie-frame-or-window)))))

(deftest ie-frame-or-window-rejects-non-smob (wrong-type-argument)
  (el-expr `(print (condition-case err
                       (progn (--ie-frame-or-window nil) 'no-signal)
                     (error (car err))))))

(deftest ie-arg-fboundp (t)
  (el-expr `(print (fboundp '--ie-arg))))

(deftest ie-arg-subrp (t)
  (el-expr `(print (subrp (symbol-function '--ie-arg)))))

(deftest ie-arg-rejects-non-smob (wrong-type-argument)
  (el-expr `(print (condition-case err
                       (progn (--ie-arg nil) 'no-signal)
                     (error (car err))))))

(deftest ie-device-fboundp (t)
  (el-expr `(print (fboundp '--ie-device))))

(deftest ie-device-subrp (t)
  (el-expr `(print (subrp (symbol-function '--ie-device)))))

(deftest ie-device-rejects-non-smob (wrong-type-argument)
  (el-expr `(print (condition-case err
                       (progn (--ie-device nil) 'no-signal)
                     (error (car err))))))
