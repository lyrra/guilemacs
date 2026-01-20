;;; test-gv-setf.el --- Tests for gv-define-setter and setf

(require 'cl-lib)

(test-begin "gv-setf")

;;; ============================================================
;;; Basic gv-define-setter functionality
;;; ============================================================

;; Define a simple getter for testing
(defun test-gv-get-elem (vec)
  "Get element 0 from VEC."
  (aref vec 0))

;; Define setter using gv-define-setter
(gv-define-setter test-gv-get-elem (value vec)
  `(aset ,vec 0 ,value))

(test-assert "gv-define-setter-registers-expander"
             (not (null (function-get 'test-gv-get-elem 'gv-expander))))

;;; ============================================================
;;; setf with user-defined gv-define-setter
;;; ============================================================

(let ((v (vector 10 20 30)))
  (test-equal "setf-user-defined-before" 10 (test-gv-get-elem v))
  (setf (test-gv-get-elem v) 99)
  (test-equal "setf-user-defined-after" 99 (test-gv-get-elem v)))

;;; ============================================================
;;; cl-incf with user-defined gv-define-setter
;;; ============================================================

(let ((v (vector 10 20 30)))
  (test-equal "cl-incf-user-defined-before" 10 (test-gv-get-elem v))
  (cl-incf (test-gv-get-elem v) 5)
  (test-equal "cl-incf-user-defined-after" 15 (test-gv-get-elem v)))

;;; ============================================================
;;; cl-decf with user-defined gv-define-setter
;;; ============================================================

(let ((v (vector 100 20 30)))
  (test-equal "cl-decf-user-defined-before" 100 (test-gv-get-elem v))
  (cl-decf (test-gv-get-elem v) 25)
  (test-equal "cl-decf-user-defined-after" 75 (test-gv-get-elem v)))

;;; ============================================================
;;; Built-in setf (aref) still works
;;; ============================================================

(let ((v (vector 1 2 3)))
  (test-equal "setf-aref-before" 2 (aref v 1))
  (setf (aref v 1) 42)
  (test-equal "setf-aref-after" 42 (aref v 1)))

;;; ============================================================
;;; Built-in cl-incf on aref
;;; ============================================================

(let ((v (vector 10 20 30)))
  (test-equal "cl-incf-aref-before" 20 (aref v 1))
  (cl-incf (aref v 1) 7)
  (test-equal "cl-incf-aref-after" 27 (aref v 1)))

;;; ============================================================
;;; Property-style accessor (like org-element-property)
;;; ============================================================

(defun test-gv-prop-get (prop obj)
  "Get PROP from OBJ (a vector with plist at index 0)."
  (plist-get (aref obj 0) prop))

(defun test-gv-prop-put (obj prop value)
  "Set PROP in OBJ to VALUE."
  (aset obj 0 (plist-put (aref obj 0) prop value)))

(gv-define-setter test-gv-prop-get (value prop obj)
  `(test-gv-prop-put ,obj ,prop ,value))

(let ((obj (vector (list :begin 10 :end 20))))
  (test-equal "setf-property-before" 10 (test-gv-prop-get :begin obj))
  (setf (test-gv-prop-get :begin obj) 100)
  (test-equal "setf-property-after" 100 (test-gv-prop-get :begin obj)))

(let ((obj (vector (list :begin 10 :end 20))))
  (test-equal "cl-incf-property-before" 10 (test-gv-prop-get :begin obj))
  (cl-incf (test-gv-prop-get :begin obj) 5)
  (test-equal "cl-incf-property-after" 15 (test-gv-prop-get :begin obj)))

;;; ============================================================
;;; gv-define-simple-setter
;;; ============================================================

(defun test-gv-simple-get (vec idx)
  "Get element IDX from VEC."
  (aref vec idx))

(defun test-gv-simple-set (vec idx value)
  "Set element IDX in VEC to VALUE."
  (aset vec idx value))

(gv-define-simple-setter test-gv-simple-get test-gv-simple-set)

(let ((v (vector 1 2 3 4 5)))
  (test-equal "simple-setter-before" 3 (test-gv-simple-get v 2))
  (setf (test-gv-simple-get v 2) 33)
  (test-equal "simple-setter-after" 33 (test-gv-simple-get v 2)))

;;; ============================================================
;;; Multiple setf in same form
;;; ============================================================

(let ((v1 (vector 1))
      (v2 (vector 2)))
  (setf (test-gv-get-elem v1) 11
        (test-gv-get-elem v2) 22)
  (test-equal "multiple-setf-v1" 11 (test-gv-get-elem v1))
  (test-equal "multiple-setf-v2" 22 (test-gv-get-elem v2)))

;;; ============================================================
;;; setf returns the assigned value
;;; ============================================================

(let ((v (vector 0)))
  (test-equal "setf-return-value" 42 (setf (test-gv-get-elem v) 42)))

(test-end)

(provide 'test-gv-setf)
