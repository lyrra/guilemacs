(define-module (emacs condition)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export
   (init-condition-registrations))

;;; Condition System Support
;;;
;;; This module provides handler-bind-1, the core primitive for handler-bind.
;;; handler-bind runs handlers in the dynamic extent (before unwinding),
;;; unlike condition-case which unwinds first.

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

(define (init-condition-registrations)
  "Initialize condition system registrations."
  ;; handler-bind-1 is registered via define-elisp-inline above
  #t)
