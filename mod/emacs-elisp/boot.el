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

(defun debugflag ()
  (funcall (@ (emacs-elisp runtime) debugflag)))

(defun set-debugflag! (x)
  (funcall (@ (emacs-elisp runtime) set-debugflag!)
           x))

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

(defun %functionp (object)
  (%funcall (@ (guile) procedure?) object))

(defun symbol-function (symbol)
  (let ((f (%funcall (@ (emacs-elisp runtime) symbol-function)
                     symbol)))
    (if (%funcall (@ (emacs-elisp falias) falias?) f)
        (%funcall (@ (emacs-elisp falias) falias-object) f)
      f)))

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

;(defun defvaralias (new-alias base-variable &optional docstring)
;  (let ((fluid (funcall (@ (emacs-elisp runtime) symbol-fluid)
;                        base-variable)))
;    (funcall (@ (emacs-elisp runtime) set-symbol-fluid!)
;             new-alias
;             fluid)
;    base-variable))

;;; List predicates

; FIX: cant disable: cl-preloaded: wrong-type-arg
(fset 'not #'null)

;;; Lists

(defmacro dolist (spec &rest body)
  (apply #'(lambda (var list &optional result)
             (list 'progn
                   (list 'mapc
                         (cons 'lambda (cons (list var) body))
                         list)
                   result))
         spec))

;;; Nonlocal exits

;; Helper to convert Guile exception to elisp error
;; Returns (error-symbol . error-data) pair
(defun %convert-guile-exception (key args)
  (cond
   ;; elisp-throw: (tag value) - uncaught throw becomes no-catch error
   ((eq key 'elisp-throw)
    (let ((tag (car args))
          (value (cadr args)))
      (cons 'no-catch (list tag value))))

   ;; wrong-number-of-args: (subr fmt-string (proc) #f)
   ;; where (nth 2 args) is a list containing the procedure
   ;; -> (wrong-number-of-arguments proc-name actual-count)
   ((eq key 'wrong-number-of-args)
    (let* ((fmt-args (if (> (length args) 2) (nth 2 args) nil))
           (proc (if (consp fmt-args) (car fmt-args) nil))
           (name (if (and proc (functionp proc))
                     (funcall (@ (guile) procedure-name) proc)
                   'unknown)))
      (cons 'wrong-number-of-arguments (list name 0))))

   ;; wrong-type-arg: (position message (expected got) #f)
   ;; -> (wrong-type-argument expected got)
   ((eq key 'wrong-type-arg)
    (let* ((fmt-args (if (> (length args) 2) (nth 2 args) nil))
           (expected (if (consp fmt-args) (car fmt-args) nil))
           (got (if (and (consp fmt-args) (cdr fmt-args)) (cadr fmt-args) nil)))
      (cons 'wrong-type-argument (list expected got))))

   ;; Default: pass args as-is
   (t
    (cons 'error args))))

;; condition-case using Guile's catch for 'elisp-condition.
;; Also wraps body to catch raw Guile exceptions and convert them.
(defmacro condition-case (var bodyform &rest handlers)
  (if (null handlers)
      bodyform
    (let ((key-sym (make-symbol "key"))
          (err-sym-sym (make-symbol "err-sym"))
          (err-data-sym (make-symbol "err-data"))
          (conditions-sym (make-symbol "conditions"))
          (guile-key-sym (make-symbol "guile-key"))
          (guile-args-sym (make-symbol "guile-args")))
      ;; Outer catch for elisp-condition
      `(funcall (@ (guile) catch)
                'elisp-condition
                #'(lambda ()
                    ;; Inner catch for raw Guile exceptions
                    (funcall (@ (emacs-elisp runtime) catch-all)
                             #'(lambda () ,bodyform)
                             ;; Handler receives (key args-list)
                             #'(lambda (,guile-key-sym ,guile-args-sym)
                                 (declare (lexical ,guile-key-sym ,guile-args-sym))
                                 (if (eq ,guile-key-sym 'elisp-throw)
                                     ;; Re-throw elisp throws so catch can receive them
                                     (%funcall (@ (guile) apply)
                                               (@ (guile) throw)
                                               'elisp-throw
                                               ,guile-args-sym)
                                   (if (eq ,guile-key-sym 'elisp-condition)
                                       ;; Re-throw elisp conditions directly - args-sym is (error-sym error-data)
                                       (%funcall (@ (guile) apply)
                                                 (@ (guile) throw)
                                                 'elisp-condition
                                                 ,guile-args-sym)
                                     ;; Convert Guile exceptions to elisp format
                                     (let ((converted (%convert-guile-exception ,guile-key-sym ,guile-args-sym)))
                                       (declare (lexical converted))
                                       (%funcall (@ (guile) throw)
                                                 'elisp-condition
                                                 (car converted)
                                                 (cdr converted))))))))
                #'(lambda (,key-sym ,err-sym-sym ,err-data-sym)
                    (declare (lexical ,key-sym ,err-sym-sym ,err-data-sym))
                    (let ((,conditions-sym (get ,err-sym-sym 'error-conditions))
                          ,@(if var
                                `((,var (cons ,err-sym-sym ,err-data-sym)))
                              nil))
                      (declare (lexical ,conditions-sym ,@(if var `(,var) nil)))
                      (cond
                       ,@(mapcar
                          #'(lambda (handler)
                              (let ((conds (car handler))
                                    (body (cdr handler)))
                                `(,(if (eq conds t)
                                       t
                                     (if (consp conds)
                                         `(or ,@(mapcar #'(lambda (c) `(memq ',c ,conditions-sym)) conds))
                                       `(memq ',conds ,conditions-sym)))
                                  ,@body)))
                          handlers)
                       ;; No handler matched, re-signal
                       (t (signal ,err-sym-sym ,err-data-sym)))))))))

(put 'error 'error-conditions '(error))
(put 'wrong-type-argument 'error-conditions '(wrong-type-argument error))
(put 'invalid-function 'error-conditions '(invalid-function error))
(put 'no-catch 'error-conditions '(no-catch error))
(put 'throw 'error-conditions '(throw))

;; catch uses call-with-catch (C mechanism)
;; throw is the C primitive Fthrow

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

;; Note: condition-case is defined earlier using call-with-handler.

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
