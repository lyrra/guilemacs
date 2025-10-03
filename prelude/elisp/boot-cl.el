;;; boot-cl.el --- CL bootstrap helpers for Guilemacs -*- lexical-binding: t -*-

;; Copyright (C) 2024

;; This file is part of Guilemacs.  It provides the Common Lisp
;; compatibility scaffolding needed during early bootstrap, once the
;; core runtime and `gv' are in place.

;;; Code:

;; Lightweight debugging hook; keep default false to avoid noisy bootstrap.
(defvar cl--bootstrap-debug-log nil)

(defun cl--bootstrap--log (fmt &rest args)
  (when cl--bootstrap-debug-log
    (apply #'message (concat "[boot-cl] " fmt) args)))

;; Bootstrap fallback for `cl-typep'.  `cl-preloaded.el' invokes
;; `cl-check-type' before `cl-macs.el' has been loaded, so provide a
;; conservative definition that covers the small set of type
;; descriptors touched during early bootstrap.  Once `cl-macs.el'
;; loads, its proper inline definition replaces this stub.
(unless (fboundp 'cl-typep)
  (defun cl-typep (value type)
    (cond
     ((eq type t) t)
     ((null type) nil)
     ((symbolp type)
      (let ((pred
             (cond
              ((eq type 'atom) 'atom)
              ((eq type 'symbol) 'symbolp)
              ((eq type 'keyword) 'keywordp)
              ((eq type 'integer) 'integerp)
              ((eq type 'fixnum) 'fixnump)
              ((eq type 'float) 'floatp)
              ((eq type 'number) 'numberp)
              ((eq type 'real) 'numberp)
              ((eq type 'natnum) 'natnump)
              ((eq type 'wholenump) 'wholenump)
              ((eq type 'list) 'listp)
              ((eq type 'cons) 'consp)
              ((eq type 'string) 'stringp)
              ((eq type 'vector) 'vectorp)
              ((eq type 'array) 'arrayp)
              ((eq type 'sequence) 'sequencep)
              ((eq type 'hash-table) 'hash-table-p)
              ((eq type 'function) 'functionp)
              ((eq type 'subr) 'subrp)
              ((eq type 'compiled-function) 'byte-code-function-p)
              ((eq type 'buffer) 'bufferp)
              ((eq type 'window) 'windowp)
              ((eq type 'frame) 'framep)
              ((eq type 'process) 'processp)
              ((eq type 'overlay) 'overlayp)
              ((eq type 'char) 'characterp)
              ((eq type 'boolean) (lambda (v) (or (eq v nil) (eq v t))))
              (t nil))))
        (cond
         ((functionp pred) (funcall pred value))
         (pred (funcall pred value))
         (t
          (let* ((name (symbol-name type))
                 (trial (intern-soft (concat name "p")))
                 (trial2 (unless (and trial (fboundp trial))
                           (intern-soft (concat name "-p")))))
            (cond
             ((and trial (fboundp trial)) (funcall trial value))
             ((and trial2 (fboundp trial2)) (funcall trial2 value))
             (t (eq type (type-of value)))))))))
     ((consp type)
      (let ((tag (car type)))
        (cond
         ((eq tag 'satisfies)
          (let ((fn (cadr type)))
            (if (fboundp fn)
                (funcall fn value)
              (error "Unknown predicate %S in satisfies" fn))))
         ((eq tag 'member) (memql value (cdr type)))
         ((eq tag 'not) (not (cl-typep value (cadr type))))
         ((eq tag 'and)
          (let ((types (cdr type))
                (ok t))
            (while (and ok types)
              (setq ok (cl-typep value (car types)))
              (setq types (cdr types)))
            ok))
         ((eq tag 'or)
          (let ((types (cdr type))
                (result nil))
            (while (and (not result) types)
              (setq result (cl-typep value (car types)))
              (setq types (cdr types)))
            result))
         (t (error "Unsupported type spec %S" type)))))
     (t (error "Unsupported type spec %S" type)))))

(unless (fboundp 'cl--block-wrapper)
  (defun cl--block-wrapper (value)
    value))

(defvar cl--bootstrap-class-table nil)

(defun cl--bootstrap--lookup (symbol)
  (cdr (assq symbol cl--bootstrap-class-table)))

(defun cl--bootstrap--store (symbol descriptor)
  (let ((cell (assq symbol cl--bootstrap-class-table)))
    (if cell
        (setcdr cell descriptor)
      (push (cons symbol descriptor) cl--bootstrap-class-table)))
  descriptor)

(defun cl--bootstrap--descriptor-field (descriptor plist-key index)
  (cond
   ;; Temporary plist representation used before real classes exist.
   ((and (consp descriptor) (eq (car descriptor) :cl-struct))
    (plist-get (cdr descriptor) plist-key))
   ;; Records created via cl-defstruct.
   ((and (fboundp 'recordp) (recordp descriptor))
    (let ((dtype (type-of descriptor)))
      (cond
       ;; Full cl-structure-class layout.
       ((eq dtype 'cl-structure-class)
        (pcase plist-key
          (:parents (aref descriptor 3))
          (:slots (aref descriptor 4))
          (:index-table (aref descriptor 5))
          (:tag (aref descriptor 6))
          (:named (aref descriptor 8))
          (:children (aref descriptor 10))
          (_ (condition-case nil
                 (aref descriptor index)
               (error nil)))))
       ;; cl--class and built-in-class share the same compact layout.
       ((memq dtype '(cl--class built-in-class))
        (pcase plist-key
          (:parents (aref descriptor 3))
          (:slots (aref descriptor 4))
          (:index-table (aref descriptor 5))
          ;; These descriptors do not carry tag/children/named fields.
          (:tag nil)
          (:named nil)
          (:children nil)
          (_ (condition-case nil
                 (aref descriptor index)
               (error nil)))))
       ;; No additional data for other record types at this stage.
       (t nil))))
   ;; Fallback for vector-like descriptors (should be rare).
   (descriptor
    (condition-case nil
        (aref descriptor index)
      (error nil)))
   (t nil)))

(defun cl--bootstrap--ensure-tag-witness (descriptor)
  (let ((tag (cl--bootstrap--descriptor-field descriptor :tag 6)))
    (when (symbolp tag)
      (unless (symbol-function tag)
        (fset tag :quick-object-witness-check))
      (unless (get tag 'cl-struct-type)
        (let ((named (cl--bootstrap--descriptor-field descriptor :named 8)))
          (put tag 'cl-struct-type (cons 'record named)))))))

(defun cl--bootstrap--struct-like-p (value)
  (cond
   ((and (consp value) (eq (car value) :cl-struct)) t)
   ((condition-case nil
         (let ((tag (aref value 0)))
           (and (symbolp tag)
                (or (cl--find-class tag)
                    (get tag 'cl-struct-type))
                t))
       (error nil)))
   (t nil)))

(unless (fboundp 'cl--find-class)
  (defun cl--find-class (symbol)
    (and (symbolp symbol)
         (or (get symbol 'cl--class)
             (cl--bootstrap--lookup symbol)))))

;; Add setf expander for our bootstrap cl--find-class so (setf (cl--find-class ...) ...) works.
(when (and (fboundp 'gv-define-setter)
           (not (get 'cl--find-class 'gv-expander)))
  (gv-define-setter cl--find-class (val symbol)
    `(cl--set-class! ,symbol ,val)))

(unless (fboundp 'cl--set-class!)
  (defun cl--set-class! (symbol descriptor)
    (when (symbolp symbol)
      (cl--bootstrap--log "set-class %S type=%S size=%s" symbol
                          (condition-case nil (type-of descriptor) (error :no-type))
                          (condition-case nil (length descriptor) (error :no-length)))
      (put symbol 'cl--class descriptor)
      (cl--bootstrap--store symbol descriptor)
      (cl--bootstrap--ensure-tag-witness descriptor))))

(defvar cl--bootstrap--orig-put nil)

(if (fboundp 'advice-add)
    (progn
      (cl--bootstrap--log "installing put advice")
      (defun cl--bootstrap--put-advice (orig symbol prop value)
        (if (and (eq prop 'cl--class)
                 (or (recordp value)
                     (and (consp value) (eq (car value) :cl-struct))))
            (progn
              (cl--bootstrap--log "put %S type=%S size=%s" symbol
                                  (condition-case nil (type-of value) (error :no-type))
                                  (condition-case nil (length value) (error :no-length)))
              (prog1 (funcall orig symbol prop value)
                (cl--bootstrap--store symbol value)
                (cl--bootstrap--ensure-tag-witness value)))
          (funcall orig symbol prop value)))
      (advice-add 'put :around #'cl--bootstrap--put-advice))
  (unless cl--bootstrap--orig-put
    (setq cl--bootstrap--orig-put (symbol-function 'put))
    (fset 'put
          (lambda (symbol prop value)
            (if (and (eq prop 'cl--class)
                     (or (recordp value)
                         (and (consp value) (eq (car value) :cl-struct))))
                (let ((repr (condition-case nil (prin1-to-string value)
                               (error "<#object>"))))
                  (cl--bootstrap--log "put* %S type=%S size=%s value=%s" symbol
                                      (condition-case nil (type-of value) (error :no-type))
                                      (condition-case nil (length value) (error :no-length))
                                      repr)
                  (prog1 (funcall cl--bootstrap--orig-put symbol prop value)
                    (cl--bootstrap--store symbol value)
                    (cl--bootstrap--ensure-tag-witness value)))
              (funcall cl--bootstrap--orig-put symbol prop value))))))

(unless (fboundp 'cl-struct-p)
  (defun cl-struct-p (value)
    (cl--bootstrap--struct-like-p value)))

(when (fboundp 'advice-add)
  (defun cl--bootstrap--struct-p-advice (orig value)
    (let ((result (funcall orig value)))
      (if result
          result
        (let ((fallback (cl--bootstrap--struct-like-p value)))
          (when fallback
            (message "cl-struct-p fallback satisfied for %S" value))
          fallback))))
  (advice-add 'cl-struct-p :around #'cl--bootstrap--struct-p-advice))

(unless (fboundp 'cl--class-p)
  (defun cl--class-p (value)
    (cl-struct-p value)))

(unless (fboundp 'cl--struct-class-slots)
  (defun cl--struct-class-slots (descriptor)
    (cl--bootstrap--descriptor-field descriptor :slots 4)))

(unless (fboundp 'cl--struct-class-parents)
  (defun cl--struct-class-parents (descriptor)
    (cl--bootstrap--descriptor-field descriptor :parents 3)))

(unless (fboundp 'cl--struct-class-tag)
  (defun cl--struct-class-tag (descriptor)
    (cl--bootstrap--descriptor-field descriptor :tag 6)))

(unless (fboundp 'cl--struct-class-children-sym)
  (defun cl--struct-class-children-sym (descriptor)
    (cl--bootstrap--descriptor-field descriptor :children 10)))

(provide 'boot-cl)

;;; boot-cl.el ends here
(defun cl--bootstrap--finalize-built-in (name descriptor parent-classes docstring)
  (if (and (recordp descriptor)
           (eq (type-of descriptor) 'built-in-class)
           (<= (length descriptor) 1))
      (let* ((slots (make-vector 0 nil))
             (index (make-hash-table :test 'eq :size 0))
             (inflated (record 'built-in-class
                               name
                               docstring
                               parent-classes
                               slots
                               index)))
        (cl--bootstrap--log "inflate %S -> size=%s" name (length inflated))
        inflated)
    descriptor))
