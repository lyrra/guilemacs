;;; bar.el --- Like gnus.el, sets up autoloads  -*- lexical-binding: t; -*-

;; This file sets up autoloads for functions in foo.el
;; Similar to how gnus.el (lines 2486-2618) sets up autoloads for gnus-sum functions

(require 'cl-lib)

;; Replicate gnus.el's pattern: eval-and-compile + mapc to set up autoloads
(eval-and-compile
  (mapc
   (lambda (package)
     (mapcar
      (lambda (function)
        (unless (fboundp function)
          (autoload function (car package) nil nil)))
      (cdr package)))
   '(("foo" foo-data-header foo-data-number foo-data-make))))

(provide 'bar)
;;; bar.el ends here
