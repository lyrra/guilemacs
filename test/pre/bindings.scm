;; Tests for the Scheme binding registry (emacs bindings)
;;
;; These test the binding stack operations that will replace
;; the C specpdl for introspection functions.
;;
;; Note: Tests call Scheme functions via (@ (emacs bindings) ...) from elisp.

;; =============================================================================
;; BASIC PUSH/POP TESTS
;; =============================================================================

;; Test 1: Empty stack check
(deftest binding-stack-initially-empty (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (princ (if (funcall (@ (emacs bindings) binding-stack-empty?)) t nil)))))

;; Test 2: Push increases depth
(deftest binding-push-increases-depth (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'old-value 0 nil)
    (princ (if (= (funcall (@ (emacs bindings) binding-stack-depth)) 1) t nil)))))

;; Test 3: Pop decreases depth
(deftest binding-pop-decreases-depth (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'old-value 0 nil)
    (funcall (@ (emacs bindings) pop-binding!))
    (princ (if (= (funcall (@ (emacs bindings) binding-stack-depth)) 0) t nil)))))

;; Test 4: Pop returns entry with correct symbol
(deftest binding-pop-returns-entry (foo)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'old-value 0 nil)
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (aref entry 0))))))

;; Test 5: Pop from empty returns nil (Scheme #f becomes nil)
(deftest binding-pop-empty-returns-nil (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (princ (if (null (funcall (@ (emacs bindings) pop-binding!))) t nil)))))

;; Test 6: Multiple pushes increase depth correctly
(deftest binding-multiple-pushes (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'a 1 0 nil)
    (funcall (@ (emacs bindings) push-binding!) 'b 2 0 nil)
    (funcall (@ (emacs bindings) push-binding!) 'c 3 0 nil)
    (princ (if (= (funcall (@ (emacs bindings) binding-stack-depth)) 3) t nil)))))

;; Test 7: LIFO order - most recent popped first
(deftest binding-lifo-order (c)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'a 1 0 nil)
    (funcall (@ (emacs bindings) push-binding!) 'b 2 0 nil)
    (funcall (@ (emacs bindings) push-binding!) 'c 3 0 nil)
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (aref entry 0))))))

;; =============================================================================
;; FIND-TOPLEVEL-BINDING TESTS
;; =============================================================================

;; Test 8: No binding returns nil
(deftest binding-find-toplevel-no-binding (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (princ (if (null (funcall (@ (emacs bindings) find-toplevel-binding) 'foo))
               t nil)))))

;; Test 9: Single binding returns old value
(deftest binding-find-toplevel-single (original)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'original 0 nil)
    (princ (funcall (@ (emacs bindings) find-toplevel-binding) 'foo)))))

;; Test 10: Nested bindings returns outermost old value
(deftest binding-find-toplevel-nested (first)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'first 0 nil)   ;; outermost
    (funcall (@ (emacs bindings) push-binding!) 'foo 'second 0 nil)  ;; middle
    (funcall (@ (emacs bindings) push-binding!) 'foo 'third 0 nil)   ;; innermost
    (princ (funcall (@ (emacs bindings) find-toplevel-binding) 'foo)))))

;; Test 11: Different symbols don't interfere
(deftest binding-find-toplevel-different-syms (a-value)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'a 'a-value 0 nil)
    (funcall (@ (emacs bindings) push-binding!) 'b 'b-value 0 nil)
    (princ (funcall (@ (emacs bindings) find-toplevel-binding) 'a)))))

;; =============================================================================
;; FIND-ALL-BINDINGS TESTS
;; =============================================================================

;; Test 12: Find all bindings for symbol returns correct count
(deftest binding-find-all-count (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'first 0 nil)
    (funcall (@ (emacs bindings) push-binding!) 'bar 'other 0 nil)
    (funcall (@ (emacs bindings) push-binding!) 'foo 'second 0 nil)
    (princ (if (= (length (funcall (@ (emacs bindings) find-all-bindings) 'foo)) 2)
               t nil)))))

;; =============================================================================
;; BINDING KIND TESTS
;; =============================================================================

;; Test 13: LET kind stored correctly
(deftest binding-kind-let (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'val 0 nil)
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (if (= (aref entry 2) 0) t nil))))))

;; Test 14: LET-LOCAL kind stored correctly
(deftest binding-kind-let-local (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'val 1 'some-buffer)
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (if (= (aref entry 2) 1) t nil))))))

;; Test 15: LET-DEFAULT kind stored correctly
(deftest binding-kind-let-default (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'val 2 nil)
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (if (= (aref entry 2) 2) t nil))))))

;; =============================================================================
;; WHERE (BUFFER) TESTS
;; =============================================================================

;; Test 16: Where field stored correctly
(deftest binding-where-stored (my-buffer)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'val 1 'my-buffer)
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (aref entry 3))))))

;; =============================================================================
;; OLD VALUE FIELD TESTS
;; =============================================================================

;; Test 17: Old value stored correctly
(deftest binding-old-value-stored (the-old-value)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo 'the-old-value 0 nil)
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (aref entry 1))))))

;; Test 18: Complex old value (list) stored correctly
(deftest binding-old-value-list (t)
  (el-expr `(progn
    (funcall (@ (emacs bindings) clear-binding-stack!))
    (funcall (@ (emacs bindings) push-binding!) 'foo '(a b c) 0 nil)
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (if (equal (aref entry 1) '(a b c)) t nil))))))
