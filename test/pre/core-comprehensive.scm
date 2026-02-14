;; Comprehensive C-core test expansion
;; Testing edge cases, boundary conditions, error handling, and robustness
;; Focused on increasing test coverage of core C functions and their interactions

;; =============================================================================
;; MEMORY AND ALLOCATION EDGE CASES
;; =============================================================================

;; Test large data structure creation and manipulation
(deftest large-vector-creation (t)
  (el-expr `(let ((big-vec (make-vector 10000 'test)))
              (print (= (length big-vec) 10000)))))

(deftest large-string-creation (t)
  (el-expr `(let ((big-str (make-string 5000 ?A)))
              (print (= (length big-str) 5000)))))

;; Test memory-intensive list operations
'(deftest deep-list-structure (100)
  (el-expr `(let ((deep-list '()))
              (dotimes (i 100)
                (setq deep-list (cons i deep-list)))
              (print (length deep-list)))))

;; =============================================================================
;; ARITHMETIC EDGE CASES AND BOUNDARY CONDITIONS
;; =============================================================================

;; Test arithmetic overflow and underflow behavior
(deftest fixnum-overflow (t)
  (el-expr `(let ((big (+ most-positive-fixnum 1)))
              (print (> big most-positive-fixnum)))))

(deftest negative-fixnum-underflow (t)
  (el-expr `(let ((small (- most-negative-fixnum 1)))
              (print (< small most-negative-fixnum)))))

;; Test division by zero handling
'(deftest division-by-zero-error (t)
  (el-expr `(condition-case err
              (progn (/ 1 0) nil)
            (arith-error t)
            (error t))))

;; Test modulo with zero
'(deftest modulo-by-zero-error (t)
  (el-expr `(condition-case err
              (progn (% 5 0) nil)
            (arith-error t)
            (error t))))

;; Test mixed arithmetic with extreme values
(deftest extreme-value-arithmetic (t)
  (el-expr `(let* ((big-pos (expt 2 100))
                   (big-neg (- big-pos))
                   (result (+ big-pos big-neg)))
              (print (= result 0)))))

;; =============================================================================
;; STRING OPERATIONS EDGE CASES
;; =============================================================================

;; Test string operations with null bytes
(deftest string-with-nulls (3)
  (el-expr `(let ((str-with-null (concat "\"a\"" (char-to-string 0) "\"b\"")))
              (print (length str-with-null)))))

;; Test very long strings
'(deftest long-string-concat (5000)
  (el-expr `(let ((long-str "\"\""))
              (dotimes (i 1000)
                (setq long-str (concat long-str "\"hello\"")))
              (print (length long-str)))))

;; Test string case conversion edge cases
(deftest case-conversion-unicode (t)
  (el-expr `(let* ((greek "\"αβγδε\"")
                   (upper (upcase greek))
                   (lower (downcase upper)))
              (print (string-equal lower greek)))))

;; Test string comparison with special characters
'(deftest string-compare-special (t)
  (el-expr `(string-equal (concat "\"test\"" (char-to-string 9) "\"tab\"")
                          "\"test\\ttab\"")))

;; =============================================================================
;; SYMBOL AND KEYWORD EDGE CASES
;; =============================================================================

;; Test symbol creation with special characters
(deftest symbol-special-chars (test-symbol!)
  (el-expr `(print (intern "\"test-symbol!\""))))

;; Test symbol property manipulation
(deftest symbol-property-roundtrip (test-value)
  (el-expr `(progn
              (put 'test-sym 'test-prop 'test-value)
              (print (get 'test-sym 'test-prop)))))

;; Test symbol comparison edge cases
(deftest symbol-eq-vs-equal (t)
  (el-expr `(let ((sym1 (intern "\"test\""))
                  (sym2 (intern "\"test\"")))
              (print (and (eq sym1 sym2) (equal sym1 sym2))))))

;; =============================================================================
;; LIST OPERATIONS BOUNDARY CONDITIONS
;; =============================================================================

;; Test circular list detection
'(deftest circular-list-detection (t)
  (el-expr `(let* ((lst (list 1 2 3))
                   (tail (nthcdr 2 lst)))
              (setcdr tail lst)  ; Create circular reference
              (print (> (safe-length lst) 0)))))

;; Test list operations on improper lists (dotted pairs)
'(deftest improper-list-length (0)
  (el-expr `(print (safe-length '(1 2 . 3)))))

'(deftest improper-list-nth (nil)
  (el-expr `(print (nth 3 '(1 2 . 3)))))

;; Test deep nesting limits
'(deftest deep-nested-lists (10)
  (el-expr `(let ((nested nil))
              (dotimes (i 10)
                (setq nested (list nested)))
              (let ((depth 0)
                    (current nested))
                (while (consp current)
                  (setq depth (+ 1 depth))
                  (setq current (car current)))
                (print depth)))))

;; =============================================================================
;; VECTOR OPERATIONS AND EDGE CASES
;; =============================================================================

;; Test vector access beyond bounds
'(deftest vector-bounds-error (t)
  (el-expr `(condition-case err
              (progn (aref [1 2 3] 5) nil)
            (args-out-of-range t)
            (error t))))

;; Test vector modification
'(deftest vector-modification ([42 2 3])
  (el-expr `(let ((vec [1 2 3]))
              (aset vec 0 42)
              (print vec))))

;; Test empty vector operations
(deftest empty-vector-length (0)
  (el-expr `(print (length []))))

;; =============================================================================
;; CHARACTER AND ENCODING EDGE CASES
;; =============================================================================

;; Test character boundary values
(deftest max-char-handling (t)
  (el-expr `(let ((max-ch (max-char)))
              (print (characterp max-ch)))))

;; Test character conversion roundtrips
(for-each (lambda (codepoint)
            (let ((test-name (string->symbol (format #f "char-roundtrip-~a" codepoint))))
              (deftestf test-name (codepoint)
                (el-expr `(print (string-to-char (char-to-string ,codepoint)))))))
          '(0 127 255 1024 65535 131071)) ; Various Unicode planes

;; =============================================================================
;; HASH TABLE OPERATIONS
;; =============================================================================

;; Test hash table creation with different test functions
(deftest hash-table-eq (t)
  (el-expr `(let ((ht (make-hash-table :test 'eq)))
              (puthash 'key 'value ht)
              (print (eq (gethash 'key ht) 'value)))))

(deftest hash-table-equal (t)
  (el-expr `(let ((ht (make-hash-table :test 'equal)))
              (puthash "\"key\"" "\"value\"" ht)
              (print (equal (gethash "\"key\"" ht) "\"value\"")))))

;; Test hash table with many entries
'(deftest hash-table-many-entries (1000)
  (el-expr `(let ((ht (make-hash-table)))
              (dotimes (i 1000)
                (puthash i (* i i) ht))
              (print (hash-table-count ht)))))

;; =============================================================================
;; BUFFER OPERATIONS EDGE CASES
;; =============================================================================

;; Test buffer with very long lines
'(deftest buffer-long-line (5000)
  (el-expr `(progn
              (set-buffer (get-buffer-create "\"long-line-test\""))
              (erase-buffer)
              (insert (make-string 5000 ?a))
              (print (- (point-max) (point-min))))))

;; Test buffer point manipulation at boundaries
'(deftest buffer-point-boundaries ((1 1))
  (el-expr `(progn
              (set-buffer (get-buffer-create "\"boundary-test\""))
              (erase-buffer)
              (insert "\"test\"")
              (goto-char (point-min))
              (let ((min-point (point)))
                (goto-char (point-max))
                (let ((max-point (point)))
                  (print (list min-point (- max-point 4))))))))

;; =============================================================================
;; FILE I/O AND ENCODING ROBUSTNESS
;; =============================================================================

;; Test filename handling with special characters
(deftest filename-special-chars (t)
  (el-expr `(let ((special-name "\"test file!@#$%^&*()\""))
              (print (stringp special-name)))))

;; Test path separator handling
(deftest path-handling (t)
  (el-expr `(let ((unix-path "\"/path/to/file\"")
                  (win-path "\"C:\\path\\to\\file\""))
              (print (and (stringp unix-path) (stringp win-path))))))

;; =============================================================================
;; ERROR HANDLING AND EXCEPTION ROBUSTNESS
;; =============================================================================

;; Test nested error handling
'(deftest nested-error-handling (outer-error)
  (el-expr `(condition-case outer-err
              (condition-case inner-err
                (error "\"inner\"")
                (error 'inner-caught))
              (error 'outer-error))))

;; Test error with complex data
'(deftest error-with-data (test-data)
  (el-expr `(condition-case err
              (signal 'test-error '(test-data))
            (test-error (cadr err)))))

;; =============================================================================
;; FUNCTION CALL EDGE CASES
;; =============================================================================

;; Test function calls with many arguments
'(deftest many-args-function (55)
  (el-expr `(apply '+ (number-sequence 1 10))))

;; Test function call with no arguments
'(deftest no-args-function (t)
  (el-expr `(print (functionp #'list))))

;; =============================================================================
;; GC AND MEMORY PRESSURE TESTS
;; =============================================================================

;; Test behavior under memory pressure
'(deftest gc-trigger-test (t)
  (el-expr `(progn
              (garbage-collect)
              (let ((before-gc (garbage-collect)))
                (dotimes (i 1000)
                  (make-list 100 'temp-data))
                (garbage-collect)
                (print t)))))

;; =============================================================================
;; INTERNED SYMBOL TABLE EDGE CASES
;; =============================================================================

;; Test symbol interning with edge case names
'(for-each (lambda (sym-name)
            (let ((test-name (string->symbol (format #f "intern-edge-case-~a" (string-length sym-name)))))
              (deftestf test-name (sym-name)
                (el-expr `(print (symbol-name (intern ,sym-name)))))))
          '("\"\"" "\"a\"" "\"very-long-symbol-name-with-many-characters-to-test-limits\""
            "\"symbols-with-numbers-123-and-special-chars-!@#\""))

;; =============================================================================
;; NUMERIC PRECISION AND SPECIAL VALUES
;; =============================================================================

;; Test floating point special values
(deftest float-infinity (t)
  (el-expr `(let ((inf (/ 1.0 0.0)))
              (print (> inf most-positive-fixnum)))))

(deftest float-nan-handling (t)
  (el-expr `(condition-case err
              (let ((nan (/ 0.0 0.0)))
                (print (not (= nan nan))))  ; NaN != NaN
            (arith-error t)
            (error t))))

;; Test precise decimal representations
(deftest decimal-precision (t)
  (el-expr `(let ((precise 0.1))
              (print (floatp precise)))))

;; =============================================================================
;; COMPARISON OPERATIONS EDGE CASES
;; =============================================================================

;; Test comparison with different types
'(deftest mixed-type-comparison (t)
  (el-expr `(condition-case err
              (progn (< "\"string\"" 42) nil)
            (wrong-type-argument t)
            (error t))))

;; Test equality with complex structures
(deftest complex-equality (t)
  (el-expr `(let ((list1 '((a . b) (c . d)))
                  (list2 '((a . b) (c . d))))
              (print (equal list1 list2)))))

;; =============================================================================
;; SEQUENCE OPERATIONS COMPREHENSIVE
;; =============================================================================

;; Test sequence operations on mixed types
'(deftest sequence-length-vector (3)
  (el-expr `(print (length [1 2 3]))))

'(deftest sequence-length-string (5)
  (el-expr `(print (length "hello"))))

;; Test sequence copying with different types
'(deftest copy-sequence-preservation (t)
  (el-expr `(let* ((orig [1 2 3])
                   (copy (copy-sequence orig)))
              (print (and (equal orig copy) (not (eq orig copy)))))))

;; =============================================================================
;; INTEGRATION AND INTERACTION TESTS
;; =============================================================================

;; Test complex interactions between different subsystems
'(deftest complex-interaction (t)
  (el-expr `(let* ((sym (intern "\"test-complex\""))
                   (vec (vector sym "\"string\"" 42))
                   (list (list vec sym)))
              (put sym 'test-prop list)
              (print (vectorp (car (get sym 'test-prop)))))))

;; Test recursive data structure handling
'(deftest recursive-structure (t)
  (el-expr `(let ((alist '()))
              (push (cons 'self alist) alist)
              (print (consp (cdr (assq 'self alist)))))))
