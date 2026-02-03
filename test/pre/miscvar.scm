;; ensure global variables are initialized
(deftest misc-vars-init (nil)
  (el-expr `(print (or
     ;; keyboard
     last-command-event
     last-nonmenu-event
     last-input-event))))
