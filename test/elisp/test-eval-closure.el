;;; test-eval-closure.el --- Test eval closure behavior and nadvice  -*- lexical-binding: t; -*-

;; Guilemacs only supports lexical-binding mode.
;; This test verifies that eval and the advice system work correctly
;; with lexical closures.

(test-begin "eval-closure")

;; Test 1: Basic eval'd lambda with lexical capture
(let* ((make-adder (eval '(lambda (n)
                            (lambda (x) (+ x n)))))
       (add-5 (funcall make-adder 5)))
  (test-equal "eval-lambda/basic-closure"
              15
              (funcall add-5 10)))


;; Test 1: eval with nested lambdas captures lexical bindings
(let* ((template '(apply function main args))
       (wrapper (eval `(lambda (function main)
                         (lambda (&rest args)
                           ,template))
                      t))  ; lexical binding
       (advice-fn (lambda (orig &rest args)
                    (* 2 (apply orig args))))
       (orig-fn (lambda (x) (+ x 1)))
       (wrapped (funcall wrapper advice-fn orig-fn))
       (result (funcall wrapped 5)))
  (test-equal "eval-lexical/nested-lambda-closure" 12 result))

; test without lexical bindings to eval
(let* ((template '(apply function main args))
       (wrapper (eval `(lambda (function main)
                         (lambda (&rest args)
                           ,template))))
       (advice-fn (lambda (orig &rest args)
                    (* 2 (apply orig args))))
       (orig-fn (lambda (x) (+ x 1)))
       (wrapped (funcall wrapper advice-fn orig-fn)))
  (test-equal "eval-lambda/no-lexical"
              12  ; (5+1)*2 = 12
              (funcall wrapped 5)))

;; Test 2: Explicit lambda pattern (used in nadvice.el fix)
(let* ((wrapper (lambda (function main)
                  (lambda (&rest args)
                    (apply function main args))))
       (advice-fn (lambda (orig &rest args)
                    (* 2 (apply orig args))))
       (orig-fn (lambda (x) (+ x 1)))
       (wrapped (funcall wrapper advice-fn orig-fn))
       (result (funcall wrapped 5)))
  (test-equal "explicit-lambda/nested-closure" 12 result))

(test-end)
