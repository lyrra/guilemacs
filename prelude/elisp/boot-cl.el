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
       ;; cl--class derivatives share the same first slots layout.
       ((memq dtype '(cl--class built-in-class oclosure--class))
        (pcase plist-key
          (:parents (aref descriptor 3))
          (:slots (aref descriptor 4))
          (:index-table (aref descriptor 5))
          (:allparents (condition-case nil
                           (aref descriptor 6)
                         (error nil)))
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
                (or (get tag 'cl--class)
                    (get tag 'cl-struct-type))
                t))
       (error nil)))
   (t nil)))

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

;; Slot descriptor functions - must be defined before oclosure code
(defun cl--bootstrap--slot-desc (name initform type props)
  (record 'cl-slot-descriptor name initform type props))

(unless (fboundp 'cl--make-slot-desc)
  (defun cl--make-slot-desc (name &optional initform type props)
    (cl--bootstrap--slot-desc name initform (or type t) props)))

(unless (fboundp 'cl--slot-descriptor-name)
  (defun cl--slot-descriptor-name (desc)
    (condition-case nil (aref desc 1) (error nil))))

(unless (fboundp 'cl--slot-descriptor-initform)
  (defun cl--slot-descriptor-initform (desc)
    (condition-case nil (aref desc 2) (error nil))))

(unless (fboundp 'cl--slot-descriptor-type)
  (defun cl--slot-descriptor-type (desc)
    (condition-case nil (aref desc 3) (error t))))

(unless (fboundp 'cl--slot-descriptor-props)
  (defun cl--slot-descriptor-props (desc)
    (condition-case nil (aref desc 4) (error nil))))

(defvar cl--bootstrap--oclosure-table (make-hash-table :test 'eq))

(defun cl--bootstrap--ensure-oclosure-base ()
  (unless (gethash 'oclosure cl--bootstrap--oclosure-table)
    (let* ((parent (get 'closure 'cl--class))
           (slotvec (make-vector 0 nil))
           (index-table (make-hash-table :test 'eq :size 0))
           (class (cons :cl-struct
                        (list :name 'oclosure
                              :doc "Bootstrap OClosure root"
                              :parents (if parent (list parent) nil)
                              :slots slotvec
                              :index-table index-table
                              :allparents (list 'oclosure)))))
      (puthash 'oclosure class cl--bootstrap--oclosure-table)
      (cl--set-class! 'oclosure class))))

(defun cl--bootstrap--oclosure-allparents (name parent-classes)
  (let ((parents (delete-dups
                  (apply #'append
                         (mapcar (lambda (pc)
                                   (or (cl--bootstrap--descriptor-field pc :allparents 6)
                                       (let ((pname (and (recordp pc) (aref pc 1))))
                                         (when pname (list pname)))))
                                 parent-classes)))))
    (delete-dups (cons name parents))))

(defun cl--bootstrap--oclosure-slot-desc (spec)
  (if (symbolp spec)
      (cl--make-slot-desc spec nil nil '((:read-only . t)))
    (let ((name (car spec))
          (plist (cdr spec))
          (mutable nil)
          (type nil)
          (extras '()))
      (while plist
        (let ((key (pop plist))
              (val (pop plist)))
          (pcase key
            (:mutable (setq mutable val))
            (:type (setq type val))
            (_ (push (cons key val) extras)))))
      (setq extras (assq-delete-all :read-only extras))
      (push (cons :read-only (not mutable)) extras)
      (cl--make-slot-desc name nil (or type t) extras))))

(defun cl--bootstrap--register-oclosure (name class)
  (puthash name class cl--bootstrap--oclosure-table)
  (cl--set-class! name class)
  class)

(unless (fboundp 'oclosure--class-slots)
  (defun oclosure--class-slots (class)
    (cl--bootstrap--descriptor-field class :slots 4)))

(unless (fboundp 'oclosure--class-allparents)
  (defun oclosure--class-allparents (class)
    (cl--bootstrap--descriptor-field class :allparents 6)))

(unless (fboundp 'oclosure--class-parents)
  (defun oclosure--class-parents (class)
    (cl--bootstrap--descriptor-field class :parents 3)))

(unless (fboundp 'oclosure--define)
  (defun oclosure--define (name docstring parent-names slots &rest props)
    (cl--bootstrap--ensure-oclosure-base)
    (when cl--bootstrap-debug-log
      (cl--bootstrap--log "oclosure--define %S slots=%S" name slots))
    (let* ((parent-names (or (and parent-names (copy-sequence parent-names))
                             (list 'oclosure)))
           (parent-classes (mapcar (lambda (sym)
                                     (or (get sym 'cl--class)
                                         (prog1 nil (cl--bootstrap--ensure-oclosure-base))
                                         (get sym 'cl--class)))
                                   parent-names))
           (slotdescs (mapcar #'cl--bootstrap--oclosure-slot-desc slots))
           (slotvec (apply #'vector slotdescs))
           (index-table (make-hash-table :test 'eq :size (max 1 (length slotdescs)))))
      (dotimes (i (length slotvec))
        (puthash (cl--slot-descriptor-name (aref slotvec i)) i index-table))
      (let* ((allparents (cl--bootstrap--oclosure-allparents name parent-classes))
             (class (cons :cl-struct
                          (list :name name
                                :doc docstring
                                :parents parent-classes
                                :slots slotvec
                                :index-table index-table
                                :allparents allparents)))
             (predicate (plist-get props :predicate)))
        (when predicate
          (unless (fboundp predicate)
            (fset predicate (lambda (_value) nil))))
        (cl--bootstrap--register-oclosure name class)))))

(unless (fboundp 'oclosure--build-class)
  (defun oclosure--build-class (name docstring parent-names slots)
    (cl--bootstrap--ensure-oclosure-base)
    (let* ((parent-names (or parent-names (list 'oclosure)))
           (parent-classes (mapcar (lambda (sym) (get sym 'cl--class)) parent-names))
           (slotdescs (mapcar #'cl--bootstrap--oclosure-slot-desc slots))
           (slotvec (apply #'vector slotdescs))
           (index-table (make-hash-table :test 'eq :size (max 1 (length slotdescs))))
           (allparents (cl--bootstrap--oclosure-allparents name parent-classes)))
      (dotimes (i (length slotvec))
        (puthash (cl--slot-descriptor-name (aref slotvec i)) i index-table))
      (cons :cl-struct
            (list :name name
                  :doc docstring
                  :parents parent-classes
                  :slots slotvec
                  :index-table index-table
                  :allparents allparents)))))

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

(defun cl--bootstrap--struct-record (name docstring parents slots index-table tag type named print children-sym)
  (record 'cl-structure-class
          name docstring parents slots index-table tag type named print children-sym))

(unless (fboundp 'cl--struct-new-class)
  (defun cl--struct-new-class (name docstring parents type named slots index-table children-sym tag print)
    (cl--bootstrap--struct-record name docstring parents slots index-table tag type named print children-sym)))

(unless (fboundp 'cl--struct-register-child)
  (defun cl--struct-register-child (_parent-class _tag)
    nil))
