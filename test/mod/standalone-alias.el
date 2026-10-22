;;; M60 imp-14 fixture: the real reader and evaluator path of `defalias'.
;;; `#'x' reads to (function x), so the UNEVALLED `function' form and the
;;; symbol-cell indirection both run here.  The fixture needs no installed
;;; cell that is still EMPTY: the call goes through a symbol cell.
(defun standalone-alias-source (x) (+ x 1))
(defalias 'standalone-alias-target #'standalone-alias-source)
(setq standalone-alias-test-result (standalone-alias-target 41))
