(define-module (emacs condition)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export
   (init-condition-registrations
    elisp-catch))

;;; Condition System Support
;;;
;;; This module provides:
;;; - handler-bind-1: core primitive for handler-bind (runs handlers before unwinding)
;;; - elisp-catch: Scheme implementation of elisp catch (replaces C call-with-catch)

;; handler-bind-1: elisp function that wraps elisp-handler-bind from runtime
;; Arguments: BODYFUN &rest CONDITIONS-HANDLERS
;; where CONDITIONS-HANDLERS is alternating (conditions handler conditions handler ...)
;; conditions is a list of condition symbols, handler is a function taking (err-sym . err-data)
(define-elisp-inline (handler-bind-1 bodyfun . conditions-handlers)
  "Set up error handlers around execution of BODYFUN.
BODYFUN should be a function and it is called with no arguments.
CONDITIONS should be a list of condition names (symbols).
HANDLER should be a function of one argument (the error).
Remaining arguments are additional CONDITIONS HANDLER pairs.

Unlike `condition-case', handlers run in the dynamic extent of the
signaling code, before unwinding.  If a handler returns normally,
the error continues propagating to outer handlers."
  (elisp-handler-bind bodyfun conditions-handlers))

;;; Catch/Throw Support
;;;
;;; elisp-catch implements the elisp catch semantics using Guile's catch.
;;; throw uses 'elisp-throw as the Guile key, with (tag value) as args.
;;; elisp-catch catches 'elisp-throw and compares the thrown tag.

(define (elisp-catch tag thunk)
  "Catch throws to TAG during execution of THUNK.
TAG is the elisp catch tag (a symbol).
THUNK is a zero-argument function to execute.

If (throw TAG VALUE) is called during THUNK, returns VALUE.
If throw is to a different tag, re-throws to outer catch.
If no throw occurs, returns the result of THUNK."
  (catch 'elisp-throw
    thunk
    (lambda (key thrown-tag value)
      (if (eq? thrown-tag tag)
          value
          (throw 'elisp-throw thrown-tag value)))))

(define (init-condition-registrations)
  "Initialize condition system registrations."
  ;; handler-bind-1 is registered via define-elisp-inline above
  ;; elisp-catch is exported directly for use by boot.el
  #t)
