;;; Guile Emacs Lisp -*- lexical-binding: t -*-
;;; Copyright (C) Free Software Foundation, Inc.
;;; SPDX-License-Identifier: GPL-3.0-or-later

; boot.el is loaded (by spec.scm) lazy at first elisp file compile
; so any scheme module initialization in load.scm takes place earlier

(%funcall (guile-ref (guile) format)
          (%funcall (guile-ref (guile) current-error-port))
          ";; load boot.el~%")

(defmacro @ (module symbol)
  `(guile-ref ,module ,symbol))

(defmacro @@ (module symbol)
  `(guile-private-ref ,module ,symbol))

(defmacro defun (name args &rest body)
  `(let ((proc (function (lambda ,args ,@body))))
     (%funcall (@ (emacs-elisp runtime) set-symbol-function!)
               ',name
               proc)
     (%funcall (@ (guile) set-procedure-property!)
               proc 'name ',name)
     ',name))

(defun omega () (omega))

(defun guile-tracelog (p string &rest args)
  (let* ((ap (lambda (fun &rest arguments)
               (%funcall (@ (guile) apply)
                         (@ (guile) apply)
                         (%indirect-function fun)
                         arguments)))
         (fmt (lambda (string args)
                (ap (@ (guile) format) nil string args))))
    (%funcall (if p
                  (@ (emacs-elisp runtime) guile-tracelog-print)
                (@ (emacs-elisp runtime) guile-tracelog-write))
              (fmt string args))))

(defmacro eval-and-compile (&rest body)
  `(progn
     (eval-when-compile ,@body)
     (progn ,@body)))

(defmacro %define-compiler-macro (name args &rest body)
  `(eval-and-compile
     (%funcall
      (@ (emacs-elisp runtime) set-symbol-plist!)
      ',name
      (%funcall
       (@ (guile) cons*)
       '%compiler-macro
       #'(lambda ,args ,@body)
       (%funcall (@ (emacs-elisp runtime) symbol-plist) ',name)))
     ',name))

(defmacro defsubst (name args &rest body)
  `(progn
     (defun ,name ,args ,@body)
     (eval-and-compile
       (%define-compiler-macro ,name (form)
         (%funcall (@ (guile) cons*)
                   '%funcall
                   (%funcall
                    (@ (guile) list)
                    'function
                    (%funcall (@ (guile) cons*) 'lambda ',args ',body))
                   (%funcall (@ (guile) cdr) form))))))

(eval-and-compile
  (defun eval (form)
    (%funcall (@ (emacs-elisp runtime) eval-elisp) form)))

(eval-and-compile
  (defsubst null (object)
    (declare (lexical object))
    (if object nil t))
  (defvar %gensym-counter 0)
  (defun intern-gensym (prefix)
    (setq %gensym-counter (1+ %gensym-counter))
    (%funcall (@ (guile) string->symbol)
              (%funcall (@ (guile) string-append)
                        prefix "_"
                        (%funcall (@ (guile) number->string) %gensym-counter))))
  (defun gensym (&optional prefix)
    (intern-gensym (if prefix prefix "g")))
  ;; make-symbol should create interned symbols to avoid Guile serialization errors
  (defun make-symbol (name)
    (%funcall (@ (guile) make-symbol) name)
    )
  (defun signal (error-symbol data)
    (%funcall (@ (guile) throw) 'elisp-condition error-symbol data)))

(defmacro lambda (&rest cdr)
  `#'(lambda ,@cdr))

(defmacro prog1 (first &rest body)
  (let ((temp (intern-gensym "prog1-temp")))
    `(let ((,temp ,first))
       (declare (lexical ,temp))
       ,@body
       ,temp)))

(defun interactive (&optional arg)
  nil)

(defmacro prog2 (form1 form2 &rest body)
  `(progn ,form1 (prog1 ,form2 ,@body)))

(defmacro cond (&rest clauses)
  (if (null clauses)
      nil
    (let ((first (car clauses))
          (rest (cdr clauses)))
     (if (listp first)
         (let ((condition (car first))
               (body (cdr first)))
           (if (null body)
               (let ((temp (intern-gensym "cond-temp")))
                 `(let ((,temp ,condition))
                    (declare (lexical ,temp))
                    (if ,temp
                        ,temp
                      (cond ,@rest))))
             `(if ,condition
                  (progn ,@body)
                (cond ,@rest))))
       (signal 'wrong-type-argument `(listp ,first))))))

(defmacro and (&rest conditions)
  (cond ((null conditions) t)
        ((null (cdr conditions)) (car conditions))
        (t `(if ,(car conditions)
                (and ,@(cdr conditions))
              nil))))

(defmacro or (&rest conditions)
  (cond ((null conditions) nil)
        ((null (cdr conditions)) (car conditions))
        (t (let ((temp (intern-gensym "cond-body-temp")))
             `(let ((,temp ,(car conditions)))
                (declare (lexical ,temp))
                (if ,temp
                    ,temp
                  (or ,@(cdr conditions))))))))

(defmacro lexical-let (bindings &rest body)
  (labels ((loop (list vars)
             (if (null list)
                 `(let ,bindings
                    (declare (lexical ,@vars))
                    ,@body)
               (loop (cdr list)
                     (if (consp (car list))
                         `(,(car (car list)) ,@vars)
                       `(,(car list) ,@vars))))))
    (loop bindings '())))

(defmacro lexical-let* (bindings &rest body)
  (labels ((loop (list vars)
             (if (null list)
                 `(let* ,bindings
                    (declare (lexical ,@vars))
                    ,@body)
               (loop (cdr list)
                     (if (consp (car list))
                         (cons (car (car list)) vars)
                       (cons (car list) vars))))))
    (loop bindings '())))

(defmacro while (test &rest body)
  (let ((loop (intern-gensym "while-loop")))
    `(labels ((,loop ()
                 (if ,test
                     (progn ,@body (,loop))
                   nil)))
       (,loop))))

(defmacro unwind-protect (bodyform &rest unwindforms)
  `(%funcall (@ (guile) dynamic-wind)
             #'(lambda () nil)
             #'(lambda () ,bodyform)
             #'(lambda () ,@unwindforms)))

(defmacro when (cond &rest body)
  `(if ,cond
       (progn ,@body)))

(defmacro unless (cond &rest body)
  `(when (not ,cond)
     ,@body))

;(defun symbolp (object)
; (%funcall (@ (guile) symbol?) object))

(defun %functionp (object)
  (%funcall (@ (guile) procedure?) object))

(defun symbol-function (symbol)
  (let ((f (%funcall (@ (emacs-elisp runtime) symbol-function)
                     symbol)))
    (if (%funcall (@ (emacs-elisp falias) falias?) f)
        (%funcall (@ (emacs-elisp falias) falias-object) f)
      f)))

(defun eval (form)
  (%funcall (@ (emacs-elisp runtime) eval-elisp) form))

(defun %indirect-function (object)
  (cond
   ((%functionp object)
    object)
   ((null object)
    (signal 'void-function nil))
   ((and (consp object) (eq (car object) 'macro))
    (signal 'invalid-function `(,object)))
   ((symbolp object)                    ;++ cycle detection
    (%indirect-function
     (%funcall (@ (emacs-elisp runtime) symbol-function) object)))
   ((listp object)
    (eval `(function ,object)))
   (t
    (signal 'invalid-function `(,object)))))

(defun apply (function &rest arguments)
  (%funcall (@ (guile) apply)
            (@ (guile) apply)
            (%indirect-function function)
            arguments))

(defun funcall (function &rest arguments)
  (%funcall (@ (guile) apply)
            (%indirect-function function)
            arguments))

(defun autoload-do-load (fundef &optional funname macro-only)
  (and (load (cadr fundef))
       (%indirect-function funname)))

(defun fset (symbol definition)
  (funcall (@ (emacs-elisp runtime) set-symbol-function!)
           symbol
           definition))

(defun eq (obj1 obj2)
  (if obj1
      (%funcall (@ (guile) eq?) obj1 obj2)
    (if obj2 nil t)))

(defun nthcdr (n list)
  (let ((i 0))
    (while (< i n)
      (setq list (cdr list)
            i (+ i 1)))
    list))

(defun nth (n list)
  (car (nthcdr n list)))

(defun fset (symbol definition)
  (funcall (@ (emacs-elisp runtime) set-symbol-function!)
           symbol
           (cond
            ((%funcall (@ (guile) procedure?) definition)
             definition)
            ((and (consp definition)
                  (eq (car definition) 'macro))
             (if (%funcall (@ (guile) procedure?) (cdr definition))
                 definition
               (cons 'macro
                     (funcall (@ (emacs-elisp falias) make-falias)
                              (function
                               (lambda (&rest args) (apply (cdr definition) args)))
                              (cdr definition)))))
            ((and (consp definition)
                  (eq (car definition) 'autoload))
             (if (or (eq (nth 4 definition) 'macro)
                     (eq (nth 4 definition) t))
                 (cons 'macro
                       (funcall
                        (@ (emacs-elisp falias) make-falias)
                        (function (lambda (&rest args)
                                    (apply (cdr (autoload-do-load definition symbol nil)) args)))
                        definition))
               (funcall
                (@ (emacs-elisp falias) make-falias)
                (function (lambda (&rest args)
                            (apply (autoload-do-load definition symbol nil) args)))
                definition)))
            ((and (symbolp definition)
                  (let ((fn (symbol-function definition)))
                    (and (consp fn)
                         (or (eq (car fn) 'macro)
                             (and (eq (car fn) 'autoload)
                                  (or (eq (nth 4 fn) 'macro)
                                      (eq (nth 4 fn) t)))))))
             (cons 'macro
                   (funcall
                    (@ (emacs-elisp falias) make-falias)
                    (function (lambda (&rest args) `(,definition ,@args)))
                    definition)))
            (t
             (funcall (@ (emacs-elisp falias) make-falias)
                      (function (lambda (&rest args) (apply definition args)))
                      definition))))
  definition)

(defun gload (file)
  (funcall (@ (system base compile) compile-file)
           file
           (funcall (@ (guile) symbol->keyword) 'from)
           'emacs-elisp
           (funcall (@ (guile) symbol->keyword) 'to)
           'value)
  t)

;(defun emacs-load (file)
;  (%funcall (@ (emacs-elisp runtime) emacs-load) file))

;;; Equality predicates

(defun eql (obj1 obj2)
  (if obj1
      (funcall (@ (guile) eqv?) obj1 obj2)
    (null obj2)))

(defun equal (obj1 obj2)
  (if obj1
      (funcall (@ (guile) equal?) obj1 obj2)
    (null obj2)))

;;; Symbols

;;; `symbolp' and `symbol-function' are defined above.

(fset 'symbol-name (@ (guile) symbol->string))
(fset 'symbol-value (@ (emacs-elisp runtime) symbol-value))
(fset 'set (@ (emacs-elisp runtime) set-symbol-value!))
(fset 'makunbound (@ (emacs-elisp runtime) makunbound!))
(fset 'fmakunbound (@ (emacs-elisp runtime) fmakunbound!))
(fset 'boundp (@ (emacs-elisp runtime) symbol-bound?))
(fset 'fboundp (@ (emacs-elisp runtime) symbol-fbound?))
(fset 'intern (@ (guile) string->symbol))

;(defun defvaralias (new-alias base-variable &optional docstring)
;  (let ((fluid (funcall (@ (emacs-elisp runtime) symbol-fluid)
;                        base-variable)))
;    (funcall (@ (emacs-elisp runtime) set-symbol-fluid!)
;             new-alias
;             fluid)
;    base-variable))

;;; Numerical type predicates

(defun floatp (object)
  (and (funcall (@ (guile) real?) object)
       (or (funcall (@ (guile) inexact?) object)
           (null (funcall (@ (guile) integer?) object)))))

(defun integerp (object)
  (and (funcall (@ (guile) integer?) object)
       (funcall (@ (guile) exact?) object)))

(defun numberp (object)
  (funcall (@ (guile) real?) object))

(defun wholenump (object)
  (and (integerp object) (>= object 0)))

(defun zerop (object)
  (= object 0))

;;; Numerical comparisons

;(fset '= (@ (guile) =))

;(defun /= (num1 num2)
;  (null (= num1 num2)))

;(fset '< (@ (guile) <))
;(fset '<= (@ (guile) <=))
;(fset '> (@ (guile) >))
;(fset '>= (@ (guile) >=))

;(defun max (&rest numbers)
;  (apply (@ (guile) max) numbers))

;(defun min (&rest numbers)
;  (apply (@ (guile) min) numbers))

;;; Arithmetic functions

;(fset '1+ (@ (guile) 1+))
;(fset '1- (@ (guile) 1-))
;(fset '+ (@ (guile) +))
;(fset '- (@ (guile) -))
;(fset '* (@ (guile) *))
;(fset '% (@ (guile) modulo))
;(fset 'abs (@ (guile) abs))

;;; Floating-point rounding

;(fset 'ffloor (@ (guile) floor))
;(fset 'fceiling (@ (guile) ceiling))
;(fset 'ftruncate (@ (guile) truncate))
;(fset 'fround (@ (guile) round))

;;; Numeric conversion

(defun float (arg)
  (if (numberp arg)
      (funcall (@ (guile) exact->inexact) arg)
    (signal 'wrong-type-argument `(numberp ,arg))))

;;; List predicates

; FIX: cant disable: cl-preloaded: wrong-type-arg
(fset 'not #'null)

;;; Lists

(defun setcar (cell newcar)
  (if (consp cell)
      (progn
        (funcall (@ (guile) set-car!) cell newcar)
        newcar)
    (signal 'wrong-type-argument `(consp ,cell))))

(defun setcdr (cell newcdr)
  (if (consp cell)
      (progn
        (funcall (@ (guile) set-cdr!) cell newcdr)
        newcdr)
    (signal 'wrong-type-argument `(consp ,cell))))

(defun %member (elt list test)
  (cond
   ((null list) nil)
   ((consp list)
    (if (funcall test elt (car list))
        list
      (%member elt (cdr list) test)))
   (t (signal 'wrong-type-argument `(listp ,list)))))

(defun member (elt list)
  (%member elt list #'equal))

(defun memql (elt list)
  (%member elt list #'eql))

(defun memq (elt list)
  (%member elt list #'eq))

(defun assoc (key list)
  (funcall (@ (srfi srfi-1) assoc) key list #'equal))

(defun assq (key list)
  (funcall (@ (srfi srfi-1) assoc) key list #'eq))

(defun rplaca (cell newcar)
  (funcall (@ (guile) set-car!) cell newcar)
  newcar)

(defun rplacd (cell newcdr)
  (funcall (@ (guile) set-cdr!) cell newcdr)
  newcdr)

(defmacro dolist (spec &rest body)
  (apply #'(lambda (var list &optional result)
             (list 'progn
                   (list 'mapc
                         (cons 'lambda (cons (list var) body))
                         list)
                   result))
         spec))

;;; Property lists

(defun %plist-member (plist property test)
  (cond
   ((null plist) nil)
   ((consp plist)
    (if (funcall test (car plist) property)
        (cdr plist)
      (%plist-member (cdr (cdr plist)) property test)))
   (t (signal 'wrong-type-argument `(listp ,plist)))))

(defun %plist-get (plist property test)
  (car (%plist-member plist property test)))

(defun %plist-put (plist property value test)
  (let ((x (%plist-member plist property test)))
    (if x
        (progn (setcar x value) plist)
      (cons property (cons value plist)))))

(defun plist-get (plist property)
  (%plist-get plist property #'eq))

(defun plist-put (plist property value)
  (%plist-put plist property value #'eq))

(defun plist-member (plist property)
  (%plist-member plist property #'eq))

(defun lax-plist-get (plist property)
  (%plist-get plist property #'equal))

(defun lax-plist-put (plist property value)
  (%plist-put plist property value #'equal))

(defvar plist-function (funcall (@ (guile) make-object-property)))

(defun symbol-plist (symbol)
  (funcall plist-function symbol))

(defun setplist (symbol plist)
  (funcall (funcall (@ (guile) setter) plist-function) symbol plist))

(defun get (symbol propname)
  (plist-get (symbol-plist symbol) propname))

(defun put (symbol propname value)
  (setplist symbol (plist-put (symbol-plist symbol) propname value)))

;;; Nonlocal exits

(defmacro condition-case (var bodyform &rest handlers)
  (let ((key (intern-gensym "key"))
        (error-symbol (intern-gensym "error-symbol"))
        (data (intern-gensym "data"))
        (conditions (intern-gensym "conditions")))
    (flet ((handler->cond-clause (handler)
             `((or ,@(mapcar #'(lambda (c) `(memq ',c ,conditions))
                             (if (consp (car handler))
                                 (car handler)
                               (list (car handler)))))
               ,@(cdr handler))))
      `(funcall (@ (guile) catch)
                'elisp-condition
                #'(lambda () ,bodyform)
                #'(lambda (,key ,error-symbol ,data)
                    (declare (lexical ,key ,error-symbol ,data))
                    (let ((,conditions
                           (get ,error-symbol 'error-conditions))
                          ,@(if var
                                `((,var (cons ,error-symbol ,data)))
                              '()))
                      (declare (lexical ,conditions
                                        ,@(if var `(,var) '())))
                      (cond ,@(mapcar #'handler->cond-clause handlers)
                            (t (signal ,error-symbol ,data)))))))))

(put 'error 'error-conditions '(error))
(put 'wrong-type-argument 'error-conditions '(wrong-type-argument error))
(put 'invalid-function 'error-conditions '(invalid-function error))
(put 'no-catch 'error-conditions '(no-catch error))
(put 'throw 'error-conditions '(throw))

(defvar %catch nil)

(defmacro catch (tag &rest body)
  (let ((tag-value (make-symbol "tag-value"))
        (c (make-symbol "c"))
        (data (make-symbol "data")))
    `(let ((,tag-value ,tag))
       (declare (lexical ,tag-value))
       (condition-case ,c
           (let ((%catch t))
             ,@body)
         (throw
          (let ((,data (cdr ,c)))
            (declare (lexical ,data))
            (if (eq (car ,data) ,tag-value)
                (car (cdr ,data))
              (apply #'throw ,data))))))))

(defun throw (tag value)
  (signal (if %catch 'throw 'no-catch) (list tag value)))

;; Random number generation

(defvar %random-state (funcall (@ (guile) copy-random-state)
                               (@ (guile) *random-state*)))

(defun random (&optional limit)
   (if (eq limit t)
       (setq %random-state
             (funcall (@ (guile) random-state-from-platform))))
   (funcall (@ (guile) random)
            (if (wholenump limit)
                limit
              (@ (guile) most-positive-fixnum))
            %random-state))

(defmacro save-excursion (&rest body)
  `(call-with-save-excursion #'(lambda () ,@body)))

(defmacro save-current-buffer (&rest body)
  `(call-with-save-current-buffer #'(lambda () ,@body)))

(defmacro save-restriction (&rest body)
  `(call-with-save-restriction #'(lambda () ,@body)))

(defmacro track-mouse (&rest body)
  `(call-with-track-mouse #'(lambda () ,@body)))

(defmacro setq-default (var value &rest args)
  `(progn (set-default ',var ,value)
          ,(if (null args)
               var
             `(setq-default ,@args))))

(defmacro catch (tag &rest body)
  `(call-with-catch ,tag #'(lambda () ,@body)))

(defmacro condition-case (var bodyform &rest args)
  (if (consp args)
      (let* ((handler (car args))
             (handlers (cdr args))
             (handler-conditions (car handler))
             (handler-body (cdr handler)))
        `(call-with-handler ',var
                            ',handler-conditions
                            #'(lambda () ,@handler-body)
                            #'(lambda ()
                                (condition-case ,var
                                    ,bodyform
                                  ,@handlers))))
    bodyform))

(defun backtrace-frame (nframes)
  (let* ((stack (funcall (@ (guile) make-stack) t))
         (frame (stack-ref stack nframes))
         (pname (funcall (@ (guile) frame-procedure-name) frame))
         (args (funcall (@ (guile) frame-arguments) frame)))
    (cons t (cons pname args))))

(defun guile-backtrace (&rest args)
  (interactive)
  (let* ((stack (apply (@ (guile) make-stack) t args))
         (frame (funcall (@ (guile) stack-ref) stack 1))
         (space (funcall (@ (guile) integer->char) 32)))
    (while frame
      (princ (string 32 32))
      (prin1 (funcall (@ (guile) frame-procedure-name) frame))
      (prin1 (funcall (@ (guile) frame-arguments) frame))
      (terpri)
      (setq frame (funcall (@ (guile) frame-previous) frame)))
    nil))

(defun backtrace ()
  (guile-backtrace))

(defun %set-eager-macroexpansion-mode (ignore)
  nil)

(%define-compiler-macro require (form)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (funcall #'require ,@(cdr form))))

;; FIX: provide must also run at compile time to match require behavior
;; Without this, (provide 'foo) followed by (require 'bar) where bar requires foo
;; will fail because provide wasn't executed yet at compile time
;; NOTE: At compile time we use a simple features update without running
;; after-load hooks (which can fail during early bootstrap). At load/execute
;; time we use the full provide with hooks.
(%define-compiler-macro provide (form)
  `(progn
     ;; At compile time, just update features list without hooks
     (eval-when (:compile-toplevel)
       (%funcall (@ (emacs utils) elisp-provide) ,@(cdr form)))
     ;; At load/execute time, use full provide with after-load hooks
     (eval-when (:load-toplevel :execute)
       (funcall #'provide ,@(cdr form)))))

(%funcall (guile-ref (guile) format)
          (%funcall (guile-ref (guile) current-error-port))
          ";; load boot.el done~%")
