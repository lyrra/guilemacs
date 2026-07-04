(define-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (%c defelisp))

;;; Shared elisp DEFUN reference helper.
;;; %c resolves a symbol to the elisp function in its function slot —
;;; the canonical one-liner for calling into C DEFUNs from Scheme.
;;; Duplicated in 9 modules before imp-9 consolidation.

(define (%c name) (symbol-function name))

;;; defelisp — define a delayed elisp DEFUN reference.
;;; (defelisp %foo --foo) expands to (define %foo (delay (%c '--foo))).
;;; The (delay …) wrapper ensures the DEFUN is looked up lazily,
;;; avoiding load-order sensitivity.

(define-syntax-rule (defelisp var name)
  (define var (delay (%c 'name))))
