;;; foo.el --- Like gnus-sum.el, defines struct  -*- lexical-binding: t; -*-

;; This file requires bar.el early, then defines foo-data struct later
;; Similar to how gnus-sum.el requires gnus.el then defines gnus-data

(require 'cl-lib)
(require 'inline)  ;; For define-inline

;; Require bar early (like gnus-sum requires gnus at line 61)
;; This will set up autoloads for foo-data-header pointing back to "foo"
(require 'bar)

;; The actual struct definition (like gnus-data in gnus-sum.el line 3122)
;; cl-defstruct defines foo-data-header, foo-data-number, etc.
(cl-defstruct (foo-data
               (:constructor nil)
               (:constructor foo-data-make (number header))
               (:type list))
  number header)

;; Use define-inline like gnus-sum.el does (line 3139)
;; This can trigger the autoload during compilation/macro expansion
(define-inline foo-data-pseudo-p (data)
  (inline-quote (consp (foo-data-header ,data))))

;; A function that uses the struct
(defun foo-get-header (data)
  "Get header from foo-data struct."
  (foo-data-header data))

(provide 'foo)
;;; foo.el ends here
