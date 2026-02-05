;; Phase 2 tests: Scheme bind-symbol with dynamic-wind
;; Tests PLAINVAL (fast path) and buffer-local (slow path)

;; Test 1: Basic let-binding of PLAINVAL variable
(defvar test-phase2-var 10)
(let ((test-phase2-var 42))
  (unless (= test-phase2-var 42)
    (error "Expected 42 in let, got %s" test-phase2-var)))
(unless (= test-phase2-var 10)
  (error "Expected 10 after let, got %s" test-phase2-var))
(message "Test 1 PASS: PLAINVAL let-binding")

;; Test 2: Nested let-bindings
(defvar test-p2-a 1)
(defvar test-p2-b 2)
(let ((test-p2-a 10)
      (test-p2-b 20))
  (unless (= test-p2-a 10) (error "a should be 10, got %s" test-p2-a))
  (unless (= test-p2-b 20) (error "b should be 20, got %s" test-p2-b))
  (let ((test-p2-a 100))
    (unless (= test-p2-a 100) (error "nested a should be 100"))
    (unless (= test-p2-b 20) (error "b should still be 20"))))
(unless (= test-p2-a 1) (error "a should be 1 after"))
(unless (= test-p2-b 2) (error "b should be 2 after"))
(message "Test 2 PASS: nested let-bindings")

;; Test 3: Buffer-local let-binding (FORWARDED/LOCALIZED - slow path)
(let ((buf (get-buffer-create "p2-test")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (let ((fill-column 99))
      (unless (= fill-column 99)
        (error "Expected 99 in let, got %s" fill-column)))
    (unless (= fill-column 42)
      (error "Expected 42 after let, got %s" fill-column)))
  (kill-buffer buf))
(message "Test 3 PASS: buffer-local let-binding (slow path)")

;; Test 4: unwind-protect interaction
(defvar test-p2-unwind 0)
(condition-case nil
    (let ((test-p2-unwind 42))
      (error "boom"))
  (error nil))
(unless (= test-p2-unwind 0)
  (error "Expected 0 after error unwind, got %s" test-p2-unwind))
(message "Test 4 PASS: unwind-protect with error")

;; Test 5: let* (sequential binding)
(defvar test-p2-seq 1)
(let* ((test-p2-seq 10)
       (captured test-p2-seq))
  (unless (= captured 10)
    (error "let* sequential: expected 10, got %s" captured)))
(message "Test 5 PASS: let* sequential binding")

;; Test 6: Heavy nesting stress test
(defvar test-p2-stress 0)
(let ((test-p2-stress 1))
  (let ((test-p2-stress 2))
    (let ((test-p2-stress 3))
      (let ((test-p2-stress 4))
        (let ((test-p2-stress 5))
          (unless (= test-p2-stress 5)
            (error "Depth 5: expected 5")))
        (unless (= test-p2-stress 4)
          (error "Depth 4: expected 4")))
      (unless (= test-p2-stress 3)
        (error "Depth 3: expected 3")))
    (unless (= test-p2-stress 2)
      (error "Depth 2: expected 2")))
  (unless (= test-p2-stress 1)
    (error "Depth 1: expected 1")))
(unless (= test-p2-stress 0)
  (error "Depth 0: expected 0"))
(message "Test 6 PASS: deep nesting stress test")

;; Test 7: Multiple different buffer-local vars
(let ((buf (get-buffer-create "p2-multi")))
  (with-current-buffer buf
    (let ((fill-column 42)
          (tab-width 8)
          (truncate-lines t))
      (unless (= fill-column 42) (error "fill-column wrong"))
      (unless (= tab-width 8) (error "tab-width wrong"))
      (unless truncate-lines (error "truncate-lines wrong"))))
  (kill-buffer buf))
(message "Test 7 PASS: multiple buffer-local let-bindings")

;; Test 8: Buffer-local with buffer switch during let
(let ((b1 (get-buffer-create "p2-b1"))
      (b2 (get-buffer-create "p2-b2")))
  (with-current-buffer b1
    (setq-local fill-column 11))
  (with-current-buffer b2
    (setq-local fill-column 22))
  (with-current-buffer b1
    (let ((fill-column 99))
      (with-current-buffer b2
        ;; Should see b2's value, not 99
        (unless (= fill-column 22)
          (error "In b2 during let: expected 22, got %s" fill-column))))
    (unless (= fill-column 11)
      (error "In b1 after let: expected 11, got %s" fill-column)))
  (kill-buffer b1)
  (kill-buffer b2))
(message "Test 8 PASS: buffer switch during let-binding")

;; Test 9: Validate hash consistency after all operations
(let ((buf (get-buffer-create "p2-validate")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (let ((fill-column 99))
      (validate-buffer-local-hash buf))
    (validate-buffer-local-hash buf))
  (kill-buffer buf))
(message "Test 9 PASS: hash validation after let-binding")

;; Test 10: condition-case with let-binding
(defvar test-p2-cc 0)
(condition-case err
    (let ((test-p2-cc 42))
      (+ 1 2))
  (error (message "unexpected error: %s" err)))
(unless (= test-p2-cc 0)
  (error "condition-case: expected 0, got %s" test-p2-cc))
(message "Test 10 PASS: condition-case with let-binding")

;; Test 11: Rapid binding/unbinding cycle
(defvar test-p2-rapid 0)
(dotimes (i 1000)
  (let ((test-p2-rapid (1+ i)))
    nil))
(unless (= test-p2-rapid 0)
  (error "Rapid cycle: expected 0, got %s" test-p2-rapid))
(message "Test 11 PASS: 1000 rapid bind/unbind cycles")

;; Test 12: PLAINVAL → LOCALIZED transition during let
;; Regression test for scm_to_pointer crash: if make-local-variable is
;; called during a let body, the symbol's redirect changes from PLAINVAL
;; to LOCALIZED.  The unwind must not overwrite the BLV pointer in slot 4
;; with the saved old value — it must use set-default instead.
(defvar test-p2-mlv "initial" "Variable for make-local-variable-during-let test.")
(let ((test-p2-mlv nil))
  (with-temp-buffer
    (make-local-variable 'test-p2-mlv)
    (setq test-p2-mlv "local-val")))
(unless (equal test-p2-mlv "initial")
  (error "make-local-during-let: expected \"initial\", got %S" test-p2-mlv))
(message "Test 12 PASS: PLAINVAL->LOCALIZED transition during let")

;; Test 13: Same, but with "" default (the value that triggered scm_to_pointer)
(defvar test-p2-mlv2 "" "Variable with empty-string default.")
(let ((test-p2-mlv2 nil))
  (with-temp-buffer
    (make-local-variable 'test-p2-mlv2)
    (setq test-p2-mlv2 "local")))
(unless (equal test-p2-mlv2 "")
  (error "make-local-during-let (empty string): expected \"\", got %S" test-p2-mlv2))
(message "Test 13 PASS: PLAINVAL->LOCALIZED with \"\" default")

;; Test 14: Transition during let + error unwind
(defvar test-p2-mlv3 "safe" "Variable for error-during-transition test.")
(condition-case nil
    (let ((test-p2-mlv3 nil))
      (with-temp-buffer
        (make-local-variable 'test-p2-mlv3)
        (setq test-p2-mlv3 "local")
        (error "boom")))
  (error nil))
(unless (equal test-p2-mlv3 "safe")
  (error "transition+error: expected \"safe\", got %S" test-p2-mlv3))
(message "Test 14 PASS: PLAINVAL->LOCALIZED + error unwind")

;; Test 15: Transition with set-default inside let body
(defvar test-p2-mlv4 "orig" "Variable for set-default-during-let test.")
(let ((test-p2-mlv4 nil))
  (set-default 'test-p2-mlv4 "changed-default")
  (with-temp-buffer
    (make-local-variable 'test-p2-mlv4)
    (setq test-p2-mlv4 "local")))
(unless (equal test-p2-mlv4 "orig")
  (error "set-default+transition: expected \"orig\", got %S" test-p2-mlv4))
(message "Test 15 PASS: set-default + PLAINVAL->LOCALIZED during let")

(message "All Phase 2 tests passed!")
