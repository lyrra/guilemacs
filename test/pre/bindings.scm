;; Tests for the Scheme binding registry (emacs bindings)
;;
;; These test the binding stack operations that will replace
;; the C specpdl for introspection functions.
;;
;; Note: Tests call Scheme functions via (@ (emacs bindings) ...) from elisp.

(letrec-syntax
    ((testbind
      (syntax-rules ()
        ((_ (name args) () (binds ...) body ...)
         (deftest name args
           (el-expr `(progn
                      (funcall (@ (emacs bindings) clear-binding-stack!))
                      binds ...
                      body ...))))
        ((_ (name args) ((a b c d) . binds) acc body ...)
         (testbind (name args) binds
                   ((funcall (@ (emacs bindings) push-binding!) a b c d) . acc)
                   body ...))))
     (test
      (syntax-rules ()
        ((_ name args body ...)
         (deftest name args
           (el-expr `(progn
                      (funcall (@ (emacs bindings) clear-binding-stack!))
                      body ...)))))))

  ;; =============================================================================
  ;; BASIC PUSH/POP TESTS
  ;; =============================================================================

  ;; Test 1: Empty stack check
  (test binding-stack-initially-empty (t)
    (princ (if (funcall (@ (emacs bindings) binding-stack-empty?)) t nil)))
  ;; Test 2: Push increases depth
  (testbind (binding-push-increases-depth (t))
            (('foo 'old-value 0 nil)) ()
    (princ (if (= (funcall (@ (emacs bindings) binding-stack-depth)) 1) t nil)))


  ;; Test 3: Pop decreases depth
  (testbind (binding-pop-decreases-depth (t))
            (('foo 'old-value 0 nil)) ()
    (funcall (@ (emacs bindings) pop-binding!))
    (princ (if (= (funcall (@ (emacs bindings) binding-stack-depth)) 0) t nil)))
  ;; Test 4: Pop returns entry with correct symbol
  (testbind (binding-pop-returns-entry (foo))
            (('foo 'old-value 0 nil)) ()
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (aref entry 0))))
  ;; Test 5: Pop from empty returns nil (Scheme #f becomes nil)
  (test binding-pop-empty-returns-nil (t)
    (princ (if (null (funcall (@ (emacs bindings) pop-binding!))) t nil)))
  ;; Test 6: Multiple pushes increase depth correctly
  (testbind (binding-multiple-pushes (t))
            (('c 3 0 nil) ('b 2 0 nil) ('a 1 0 nil)) ()
    (princ (if (= (funcall (@ (emacs bindings) binding-stack-depth)) 3) t nil)))
  ;; Test 7: LIFO order - most recent popped first
  (testbind (binding-lifo-order (c))
            (('c 3 0 nil) ('b 2 0 nil) ('a 1 0 nil)) ()
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (aref entry 0))))

  ;; =============================================================================
  ;; FIND-TOPLEVEL-BINDING TESTS
  ;; =============================================================================

  ;; Test 8: No binding returns nil
  (test binding-find-toplevel-no-binding (t)
    (princ (if (null (funcall (@ (emacs bindings) find-toplevel-binding) 'foo))
               t nil)))

  ;; Test 9: Single binding returns old value
  (testbind (binding-find-toplevel-single (original))
            (('foo 'original 0 nil)) ()
    (princ (funcall (@ (emacs bindings) find-toplevel-binding) 'foo)))

  ;; Test 10: Nested bindings returns outermost old value
  (testbind (binding-find-toplevel-nested (first))
            (('foo 'third 0 nil)   ;; innermost
             ('foo 'second 0 nil)  ;; middle
             ('foo 'first 0 nil))  ;; outermost
            ()
    (princ (funcall (@ (emacs bindings) find-toplevel-binding) 'foo)))

  ;; Test 11: Different symbols don't interfere
  (testbind (binding-find-toplevel-different-syms (a-value))
            (('b 'b-value 0 nil) ('a 'a-value 0 nil)) ()
    (princ (funcall (@ (emacs bindings) find-toplevel-binding) 'a)))

  ;; =============================================================================
  ;; FIND-ALL-BINDINGS TESTS
  ;; =============================================================================

  ;; Test 12: Find all bindings for symbol returns correct count
  (testbind (binding-find-all-count (t))
            (('foo 'second 0 nil) ('bar 'other 0 nil) ('foo 'first 0 nil)) ()
    (princ (if (= (length (funcall (@ (emacs bindings) find-all-bindings) 'foo)) 2)
               t nil)))

  ;; =============================================================================
  ;; BINDING KIND TESTS
  ;; =============================================================================

  ;; Test 13: LET kind stored correctly
  (testbind (binding-kind-let (t))
            (('foo 'val 0 nil)) ()
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (if (= (aref entry 2) 0) t nil))))

  ;; Test 14: LET-LOCAL kind stored correctly
  (testbind (binding-kind-let-local (t))
            (('foo 'val 1 'some-buffer)) ()
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (if (= (aref entry 2) 1) t nil))))

  ;; Test 15: LET-DEFAULT kind stored correctly
  (testbind (binding-kind-let-default (t))
        (('foo 'val 2 nil)) ()
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (if (= (aref entry 2) 2) t nil))))

  ;; =============================================================================
  ;; WHERE (BUFFER) TESTS
  ;; =============================================================================

  ;; Test 16: Where field stored correctly
  (testbind (binding-where-stored (my-buffer))
            (('foo 'val 1 'my-buffer)) ()
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (aref entry 3))))

  ;; =============================================================================
  ;; OLD VALUE FIELD TESTS
  ;; =============================================================================

  ;; Test 17: Old value stored correctly
  (testbind (binding-old-value-stored (the-old-value))
            (('foo 'the-old-value 0 nil)) ()
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (aref entry 1))))

  ;; Test 18: Complex old value (list) stored correctly
  (testbind (binding-old-value-list (t))
            (('foo '(a b c) 0 nil)) ()
    (let ((entry (funcall (@ (emacs bindings) pop-binding!))))
      (princ (if (equal (aref entry 1) '(a b c)) t nil))))

  )
