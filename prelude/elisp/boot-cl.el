;;; boot-cl.el --- CL bootstrap helpers for Guilemacs -*- lexical-binding: t -*-

;; Copyright (C) 2024

;; This file is part of Guilemacs.  It provides the Common Lisp
;; compatibility scaffolding needed during early bootstrap, once the
;; core runtime and `gv' are in place.

;;; Code:

;; Lightweight debugging hook; keep default false to avoid noisy bootstrap.
(defvar cl--bootstrap-debug-log nil)
(defvar cl--bootstrap--orig-signal nil)
(unless cl--bootstrap--orig-signal
  (setq cl--bootstrap--orig-signal (symbol-function 'signal))
  (fset 'signal
        (lambda (sym data)
          (when cl--bootstrap-debug-log
            (pcase sym
              ('wrong-type-argument
               (when (and (consp data) (eq (car data) 'cl-slot-descriptor))
                 (cl--bootstrap--log "signal wrong-type-argument for cl-slot-descriptor; data=%S" data)
                 (let ((bt (with-output-to-string (backtrace))))
                   (cl--bootstrap--log "%s" bt))))
              ('void-function
               (cl--bootstrap--log "signal void-function %S" data)
               (let ((bt (with-output-to-string (backtrace))))
                 (cl--bootstrap--log "%s" bt)))
              ('void-variable
               (cl--bootstrap--log "signal void-variable %S" data)
               (let ((bt (with-output-to-string (backtrace))))
                 (cl--bootstrap--log "%s" bt)))))
          (funcall cl--bootstrap--orig-signal sym data))))

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
    (when (and cl--bootstrap-debug-log (eq type 'cl-slot-descriptor))
      (cl--bootstrap--log "cl-typep checking value=%S for type=cl-slot-descriptor, value-type=%S"
                          value
                          (condition-case nil (type-of value) (error 'unknown))))
    (when (and (eq type 'cl-slot-descriptor) (null value))
      (cl--bootstrap--log "cl-typep got NIL for cl-slot-descriptor; dumping backtrace")
      (let ((bt (with-output-to-string (backtrace))))
        (cl--bootstrap--log "%s" bt)))
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
            (when (and cl--bootstrap-debug-log (eq type 'cl-slot-descriptor))
              (cl--bootstrap--log "  trial=%S fboundp=%S trial2=%S fboundp2=%S type-of-value=%S"
                                  trial (and trial (fboundp trial))
                                  trial2 (and trial2 (fboundp trial2))
                                  (condition-case nil (type-of value) (error 'unknown))))
            (cond
             ((and trial (fboundp trial)) (funcall trial value))
             ((and trial2 (fboundp trial2)) (funcall trial2 value))
             (t
              (let ((result (eq type (type-of value))))
                (when (and cl--bootstrap-debug-log (eq type 'cl-slot-descriptor))
                  (cl--bootstrap--log "  type-of comparison: type=%S type-of-value=%S result=%S"
                                      type (condition-case nil (type-of value) (error 'unknown)) result))
                result))))))))
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
  (when (null name)
    (error "cl--bootstrap--slot-desc called with nil name! initform=%S type=%S props=%S"
           initform type props))
  (when (and (symbolp name)
             (let ((probe (intern-soft (symbol-name name))))
               (not (eq probe name))))
    (cl--bootstrap--log "slot-desc got uninterned symbol name=%S" name))
  (when cl--bootstrap-debug-log
    (cl--bootstrap--log "slot-desc name=%S initform=%S type=%S props=%S"
                        name initform type props))
  (record 'cl-slot-descriptor name initform type props))

(unless (fboundp 'cl--make-slot-desc)
  (defun cl--make-slot-desc (name &optional initform type props)
    (cl--bootstrap--slot-desc name initform (or type t) props)))

(unless (fboundp 'cl--slot-descriptor-name)
  (defun cl--slot-descriptor-name (desc)
    (when (null desc)
      (message "[boot-cl] ERROR: cl--slot-descriptor-name called with nil desc!")
      (message "[boot-cl]   Current file being loaded: %S" load-file-name)
      (message "[boot-cl]   Stack trace (first 20 frames):")
      (let ((i 0))
        (while (< i 20)
          (let ((frame (condition-case nil (backtrace-frame i) (error nil))))
            (when frame
              (message "    frame %S: %S" i frame)))
          (setq i (1+ i))))
      (error "nil slot descriptor - see backtrace above"))
    (condition-case nil (aref desc 1) (error nil)))

  (when (fboundp 'advice-add)
    (advice-add 'cl--slot-descriptor-name :before
                (lambda (desc)
                  (when (and cl--bootstrap-debug-log (null desc))
                    (cl--bootstrap--log "cl--slot-descriptor-name received nil (advice)"))))))

(unless (fboundp 'cl--slot-descriptor-initform)
  (defun cl--slot-descriptor-initform (desc)
    (condition-case nil (aref desc 2) (error nil))))

(unless (fboundp 'cl--slot-descriptor-type)
  (defun cl--slot-descriptor-type (desc)
    (condition-case nil (aref desc 3) (error t))))

(unless (fboundp 'cl--slot-descriptor-props)
  (defun cl--slot-descriptor-props (desc)
    (condition-case nil (aref desc 4) (error nil))))

(unless (fboundp 'oclosure--slot-mutable-p)
  (defun oclosure--slot-mutable-p (slotdesc)
    (let* ((props (cl--slot-descriptor-props slotdesc))
           (read-only
            (cond
             ((null props) nil)
             ((and (consp props) (consp (car props)))
              (let ((cell (assoc :read-only props)))
                (and cell (cdr cell))))
             ((and (consp props) (keywordp (car props)))
              (plist-get props :read-only))
             (t nil))))
      (not read-only))))

(unless (fboundp 'oclosure--defstruct-make-copiers)
  (defun oclosure--defstruct-make-copiers (_copiers _slotdescs _name)
    (when cl--bootstrap-debug-log
      (cl--bootstrap--log "Skipping copier generation during bootstrap for %S" _name))
    nil))

(unless (fboundp 'cl-generic--method-qualifier-p)
  (defun cl-generic--method-qualifier-p (x)
    (not (listp x))))

(unless (fboundp 'cl--generic-get-dispatcher)
  (defun cl--generic-get-dispatcher (&rest _dispatch)
    ;; During early bootstrap we just skip precomputed dispatch caching.
    nil))

(defvar cl--generic-compiler (lambda (exp) (eval exp t)))

(unless (fboundp 'cl-generic-generalizers)
  (defun cl-generic-generalizers (_specializer)
    ;; Let compile-time prefill fall back to the default catch-all generalizer.
    nil))

(defvar cl--generic-t-generalizer nil)

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
  (when cl--bootstrap-debug-log
    (cl--bootstrap--log "oclosure-slot-desc spec=%S" spec))
  (let ((result
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
             (cl--make-slot-desc name nil (or type t) extras)))))
    (when cl--bootstrap-debug-log
      (cl--bootstrap--log "oclosure-slot-desc result=%S type=%S"
                          result
                          (condition-case nil (type-of result) (error 'error))))
    result))

(defun cl--bootstrap--register-oclosure (name class)
  (puthash name class cl--bootstrap--oclosure-table)
  (cl--set-class! name class)
  (when cl--bootstrap-debug-log
    (cl--bootstrap--log "oclosure registered: %S, returning..." name))
  class)

(unless (fboundp 'oclosure--class-slots)
  (when cl--bootstrap-debug-log
    (cl--bootstrap--log "Defining bootstrap oclosure--class-slots"))
  (defun oclosure--class-slots (class)
    (let* ((raw (cl--bootstrap--descriptor-field class :slots 4))
           (result (if (vectorp raw)
                       (append raw nil)
                     raw)))
      (when cl--bootstrap-debug-log
        (cl--bootstrap--log "oclosure--class-slots class=%S result=%S"
                            (condition-case nil (type-of class) (error 'unknown))
                            (condition-case nil
                                (if (vectorp raw) :vector :other)
                              (error :err)))
        (when (and result cl--bootstrap-debug-log)
          (cl--bootstrap--log "  list-len=%S" (length result))))
      result)))

(unless (fboundp 'oclosure--class-allparents)
  (defun oclosure--class-allparents (class)
    (cl--bootstrap--descriptor-field class :allparents 6)))

(unless (fboundp 'oclosure--class-parents)
  (defun oclosure--class-parents (class)
    (cl--bootstrap--descriptor-field class :parents 3)))

(unless (fboundp 'oclosure--define)
  (when cl--bootstrap-debug-log
    (cl--bootstrap--log "Defining bootstrap oclosure--define"))
  (defun oclosure--define (name docstring parent-names slots &rest props)
    (when cl--bootstrap-debug-log
      (cl--bootstrap--log "BOOTSTRAP oclosure--define called: %S parent-names=%S slots=%S" name parent-names slots))
    (cl--bootstrap--ensure-oclosure-base)
    (let* ((parent-names (or (and parent-names (copy-sequence parent-names))
                             (list 'oclosure)))
           (parent-classes (mapcar (lambda (sym)
                                     (or (get sym 'cl--class)
                                         (prog1 nil (cl--bootstrap--ensure-oclosure-base))
                                         (get sym 'cl--class)))
                                   parent-names))
           ;; Merge parent slots with child slots
           (parent-slots (if (and parent-classes (car parent-classes))
                            (let ((pslots (cl--bootstrap--descriptor-field (car parent-classes) :slots 4)))
                              (if (vectorp pslots)
                                  (append (mapcar (lambda (i) (aref pslots i))
                                                 (number-sequence 0 (1- (length pslots))))
                                          nil)
                                nil))
                          nil))
           (child-slotdescs (mapcar #'cl--bootstrap--oclosure-slot-desc slots))
           (all-slotdescs (append parent-slots child-slotdescs))
           (slotvec (apply #'vector all-slotdescs))
           (index-table (make-hash-table :test 'eq :size (max 1 (length all-slotdescs)))))
      (when cl--bootstrap-debug-log
        (cl--bootstrap--log "  parent-slots=%S child-slots=%S total-slots=%S"
                            (length (or parent-slots '()))
                            (length child-slotdescs)
                            (length all-slotdescs)))
      (dotimes (i (length slotvec))
        (let ((slot (aref slotvec i)))
          (when (null slot)
            (message "[boot-cl] ERROR in oclosure--define: nil slot at index %S for %S" i name)
            (message "[boot-cl]   all-slotdescs length: %S" (length all-slotdescs))
            (message "[boot-cl]   parent-slots: %S" parent-slots)
            (message "[boot-cl]   child-slotdescs: %S" child-slotdescs)
            (error "nil slot descriptor in oclosure--define!"))
          (puthash (cl--slot-descriptor-name slot) i index-table)))
      (let* ((allparents (cl--bootstrap--oclosure-allparents name parent-classes))
             (class (cons :cl-struct
                          (list :name name
                                :doc docstring
                                :parents parent-classes
                                :slots slotvec
                                :index-table index-table
                                :allparents allparents)))
             (pred (lambda (oclosure)
                     (let ((type (condition-case nil
                                     (and (functionp oclosure)
                                          (aref oclosure 0))
                                   (error nil))))
                       (when (symbolp type)
                         (let ((type-class (get type 'cl--class)))
                           (when type-class
                             (let ((allparents (cl--bootstrap--descriptor-field type-class :allparents 6)))
                               (and allparents (memq name allparents)))))))))
             (predname (or (plist-get props :predicate)
                           (intern (format "%s--internal-p" name)))))
        (defalias predname pred)
        (put name 'cl-deftype-satisfies predname)
        (when cl--bootstrap-debug-log
          (cl--bootstrap--log "BOOTSTRAP oclosure--define about to return, oclosure--define is: %S"
                              (condition-case nil (symbol-function 'oclosure--define) (error 'error))))
        (cl--bootstrap--register-oclosure name class)
        ;; Mimic what the real oclosure--define does: mark slot names
        (condition-case err
            (let ((slots-vec (cl--bootstrap--descriptor-field class :slots 4)))
              (when (vectorp slots-vec)
                (when cl--bootstrap-debug-log
                  (cl--bootstrap--log "mark-slots class=%S len=%S" name (length slots-vec)))
                (dotimes (i (length slots-vec))
                  (let ((slot (aref slots-vec i)))
                    (when cl--bootstrap-debug-log
                      (cl--bootstrap--log "  mark slot[%S]=%S type=%S" i slot
                                          (condition-case nil (type-of slot) (error :no-type))))
                    (when slot
                      (put (cl--slot-descriptor-name slot) 'slot-name t))))))
          (error
           (message "[boot-cl] ERROR in slot marking: %S" err)
           (error err)))))))

(unless (fboundp 'oclosure--build-class)
  (defun oclosure--build-class (name docstring parent-names slots)
    (cl--bootstrap--ensure-oclosure-base)
    (let* ((parent-names (or parent-names (list 'oclosure)))
           (parent-classes (mapcar (lambda (sym) (get sym 'cl--class)) parent-names))
           ;; Merge parent slots with child slots
           (parent-slots (if (and parent-classes (car parent-classes))
                            (let ((pslots (cl--bootstrap--descriptor-field (car parent-classes) :slots 4)))
                              (if (vectorp pslots)
                                  (append (mapcar (lambda (i) (aref pslots i))
                                                 (number-sequence 0 (1- (length pslots))))
                                          nil)
                                nil))
                          nil))
           (child-slotdescs (mapcar #'cl--bootstrap--oclosure-slot-desc slots))
           (all-slotdescs (append parent-slots child-slotdescs))
           (slotvec (apply #'vector all-slotdescs))
           (index-table (make-hash-table :test 'eq :size (max 1 (length all-slotdescs))))
           (allparents (cl--bootstrap--oclosure-allparents name parent-classes)))
      (dotimes (i (length slotvec))
        (let ((slot (aref slotvec i)))
          (when (null slot)
            (message "[boot-cl] ERROR in oclosure--build-class: nil slot at index %S for %S" i name)
            (message "[boot-cl]   all-slotdescs length: %S" (length all-slotdescs))
            (message "[boot-cl]   parent-slots: %S" parent-slots)
            (message "[boot-cl]   child-slotdescs: %S" child-slotdescs)
            (error "nil slot descriptor in oclosure--build-class!"))
          (puthash (cl--slot-descriptor-name slot) i index-table)))
      (cons :cl-struct
            (list :name name
                  :doc docstring
                  :parents parent-classes
                  :slots slotvec
                  :index-table index-table
                  :allparents allparents)))))

;;; Essential macros needed during bootstrap
;;; These macros MUST be defined before any code that uses them gets compiled

(defmacro save-current-buffer (&rest body)
  "Record which buffer is current; execute BODY; make that buffer current.
This is implemented as a macro that expands to call-with-save-current-buffer."
  `(call-with-save-current-buffer #'(lambda () ,@body)))

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
    (message "[boot-cl] cl--struct-new-class called: name=%S slots=%S" name slots)
    (when (vectorp slots)
      (dotimes (i (length slots))
        (let ((slot (aref slots i)))
          (when (null slot)
            (message "[boot-cl] ERROR: nil slot at index %S in cl--struct-new-class for %S" i name)
            (error "nil slot in cl--struct-new-class!")))))
    (cl--bootstrap--struct-record name docstring parents slots index-table tag type named print children-sym)))

(unless (fboundp 'cl--struct-register-child)
  (defun cl--struct-register-child (_parent-class _tag)
    nil))

;; Pre-register 'record' built-in type with empty slots
(unless (get 'record 'cl--class)
  (let* ((slots (make-vector 0 nil))
         (index-table (make-hash-table :test 'eq :size 0))
         (class (record 'built-in-class
                        'record
                        "Built-in record type"
                        nil  ; no parents
                        slots
                        index-table)))
    (put 'record 'cl--class class)))

;; Pre-register cl-slot-descriptor as a type to avoid circularity issues
;; when cl-defstruct processes type declarations like `:type (vector cl-slot-descriptor)`
(unless (get 'cl-slot-descriptor 'cl--class)
  (let* ((slots (vector (cl--make-slot-desc 'name nil t nil)
                        (cl--make-slot-desc 'initform nil t nil)
                        (cl--make-slot-desc 'type nil t nil)
                        (cl--make-slot-desc 'props nil t nil)))
         (index-table (make-hash-table :test 'eq :size 4))
         (class (record 'cl-structure-class
                        'cl-slot-descriptor
                        "Slot descriptor"
                        nil  ; no parents
                        slots
                        index-table
                        'cl-slot-descriptor  ; tag
                        'vector  ; type
                        t  ; named
                        nil  ; print
                        nil))) ; children-sym
    (puthash 'name 0 index-table)
    (puthash 'initform 1 index-table)
    (puthash 'type 2 index-table)
    (puthash 'props 3 index-table)
    (put 'cl-slot-descriptor 'cl--class class)
    (put 'cl-slot-descriptor 'cl-struct-type 'vector)))
