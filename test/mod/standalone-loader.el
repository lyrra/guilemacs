;;; A small file for the standalone Elisp loader and evaluator.

(setq standalone-loader-test-value 42)
(defun standalone-loader-test-identity (n)
  n)
(setq standalone-loader-test-result
      (standalone-loader-test-identity standalone-loader-test-value))
