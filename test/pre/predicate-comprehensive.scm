;; 2025-08-23
;; Comprehensive test for newly migrated predicate functions
;; Testing vectorp, symbolp, recordp, markerp with extensive edge cases

;; =============================================================================
;; VECTORP COMPREHENSIVE TESTS
;; =============================================================================

;; Basic vectorp tests
(deftest vectorp-empty-vector (t)
  (el-expr `(print (vectorp "[]"))))

(deftest vectorp-simple-vector (t)
  (el-expr `(print (vectorp "[1 2 3]"))))

(deftest vectorp-mixed-type-vector (t)
  (el-expr `(print (vectorp "[1 \"hello\" 'symbol]"))))

(deftest vectorp-nested-vector (t)
  (el-expr `(print (vectorp "[[1 2] [3 4]]"))))

;; Negative tests for vectorp
(deftest vectorp-list (nil)
  (el-expr `(print (vectorp '(1 2 3)))))

(deftest vectorp-string (nil)
  (el-expr `(print (vectorp "\"hello\""))))

(deftest vectorp-symbol (nil)
  (el-expr `(print (vectorp 'test))))

(deftest vectorp-number (nil)
  (el-expr `(print (vectorp 42))))

(deftest vectorp-nil (nil)
  (el-expr `(print (vectorp nil))))

'(deftest vectorp-hash-table (nil)
  (el-expr `(print (vectorp (make-hash-table)))))

;; Edge cases for vectorp
(deftest vectorp-large-vector (t)
  (el-expr `(print (vectorp (make-vector 1000 'test)))))

(deftest vectorp-vector-of-vectors (t)
  (el-expr `(let ((vec-of-vecs (vector "[1] [2] [3]")))
              (print (vectorp vec-of-vecs)))))

;; =============================================================================
;; SYMBOLP COMPREHENSIVE TESTS
;; =============================================================================

;; Basic symbolp tests
(deftest symbolp-simple-symbol (t)
  (el-expr `(print (symbolp 'hello))))

(deftest symbolp-quoted-symbol (t)
  (el-expr `(print (symbolp 'test-symbol))))

(deftest symbolp-interned-symbol (t)
  (el-expr `(print (symbolp (intern "\"dynamic-symbol\"")))))

(deftest symbolp-keyword (t)
  (el-expr `(print (symbolp :keyword))))

(deftest symbolp-nil (t)
  (el-expr `(print (symbolp nil))))

(deftest symbolp-t (t)
  (el-expr `(print (symbolp t))))

;; Negative tests for symbolp
(deftest symbolp-string (nil)
  (el-expr `(print (symbolp "\"hello\""))))

(deftest symbolp-number (nil)
  (el-expr `(print (symbolp 42))))

(deftest symbolp-vector (nil)
  (el-expr `(print (symbolp "[1 2 3]"))))

(deftest symbolp-list (nil)
  (el-expr `(print (symbolp '(1 2 3)))))

(deftest symbolp-function (nil)
  (el-expr `(print (symbolp (lambda () 42)))))

;; Edge cases for symbolp
(deftest symbolp-gensym (t)
  (el-expr `(print (symbolp (gensym)))))

(deftest symbolp-special-chars (t)
  (el-expr `(print (symbolp (intern "\"symbol-with-!@#$%\"")))))

(deftest symbolp-numeric-name (t)
  (el-expr `(print (symbolp (intern "\"123symbol\"")))))

(deftest symbolp-empty-name (t)
  (el-expr `(print (symbolp (intern "\"\"")))))

;; =============================================================================
;; MARKERP COMPREHENSIVE TESTS
;; =============================================================================

;; Basic markerp tests (should return nil for now as per implementation)
(deftest markerp-nil (nil)
  (el-expr `(print (markerp nil))))

(deftest markerp-symbol (nil)
  (el-expr `(print (markerp 'test))))

(deftest markerp-number (nil)
  (el-expr `(print (markerp 42))))

(deftest markerp-string (nil)
  (el-expr `(print (markerp "\"hello\""))))

(deftest markerp-vector (nil)
  (el-expr `(print (markerp "[1 2 3]"))))

(deftest markerp-list (nil)
  (el-expr `(print (markerp '(1 2 3)))))

;; Future marker tests (when markers are implemented)
;; These will need to be updated when marker support is added

;; =============================================================================
;; CROSS-PREDICATE CONSISTENCY TESTS
;; =============================================================================

;; Test that predicates are mutually exclusive where expected
(deftest vector-not-symbol (t)
  (el-expr `(let ((vec "[1 2 3]"))
              (print (and (vectorp vec) (not (symbolp vec)))))))

(deftest symbol-not-vector (t)
  (el-expr `(let ((sym 'test))
              (print (and (symbolp sym) (not (vectorp sym)))))))

(deftest nil-special-case (t)
  (el-expr `(print (and (symbolp nil)
                        (not (vectorp nil))
                        (not (recordp nil))
                        (not (markerp nil))))))

;; Test type consistency with related predicates
(deftest vector-is-sequence (t)
  (el-expr `(let ((vec "[1 2 3]"))
              (print (and (vectorp vec) (sequencep vec))))))

(deftest symbol-atom-consistency (t)
  (el-expr `(let ((sym 'test))
              (print (and (symbolp sym) (atom sym))))))

;; =============================================================================
;; PERFORMANCE AND STRESS TESTS
;; =============================================================================

;; Test predicates with large data structures
(deftest vectorp-large-performance (t)
  (el-expr `(let ((big-vec (make-vector 10000 'test)))
              (print (vectorp big-vec)))))

; no worries, modern elisp does tail-call-elimination
(deftest symbolp-many-symbols (t)
  (el-expr `(let* ((str "\"s\"")
                   (k (lambda (n k)
                        (if (not (> n 100))
                            (progn
                             (setq str (concat str "\"-\""))
                             (if (symbolp (intern str))
                                 (funcall k (+ n 1) k)
                                 nil))
                            t))))
              (print (funcall k 0 k)))))

;; =============================================================================
;; INTEGRATION WITH OTHER CORE FUNCTIONS
;; =============================================================================

;; Test predicates in conditional contexts
(deftest vectorp-in-if (vector-branch)
  (el-expr `(if (vectorp "[1 2 3]")
                (print 'vector-branch)
              (print 'not-vector-branch))))

(deftest symbolp-in-cond (symbol-case)
  (el-expr `(cond
              ((symbolp 'test) (print 'symbol-case))
              ((vectorp 'test) (print 'vector-case))
              (t (print 'other-case)))))

;; Test predicates with mapcar
(deftest predicates-with-mapcar ((t nil t nil))
  (el-expr `(print (mapcar "#'symbolp" '(hello 42 world "\"string\"")))))

;; =============================================================================
;; EDGE CASE COMBINATIONS
;; =============================================================================

;; Test all predicates on the same complex object
(deftest all-predicates-complex-object ((nil t nil nil))
  (el-expr `(let ((obj 'complex-symbol))
              (print (list (vectorp obj) (symbolp obj) (recordp obj) (markerp obj))))))

; vector are immutable
;; Test predicates on self-referential structures
;(deftest predicates-self-reference (t)
;  (el-expr `(let* ((vec "[nil]")
;                   (_ (aset vec 0 vec)))
;              (print (vectorp vec)))))

;; Test predicates with quoted vs unquoted forms
(deftest quoted-vs-unquoted ((t t))
  (el-expr `(print (list (symbolp 'test) (symbolp (quote test))))))
