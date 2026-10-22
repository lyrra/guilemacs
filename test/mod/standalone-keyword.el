;; Row 33 of the M60 map: the elisp reader applies the `set' function
;; cell for every :keyword form (reader.scm :1358).  An empty cell makes
;; the read of this file raise `wrong-type-arg "Wrong type to apply"'.
(defvar standalone-keyword-test-result (list :keyword-a 1 :keyword-b))
