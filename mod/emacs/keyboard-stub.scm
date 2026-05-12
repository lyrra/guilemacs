(define-module (emacs keyboard-stub)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (kb-loaded?
            init-keyboard-stub-registrations))

;;; M0 — Scaffolding milestone for the keyboard.c → Guile port.
;;;
;;; Holds no real keyboard logic.  Exists so the build / test / gating
;;; procedure described in docs/keyboard.org can be exercised end-to-end
;;; before any C body is replaced.  Subsequent milestones (M1 modifier
;;; parsing, M2 KBOARD foreign object, ...) replace or supersede this
;;; module.

(define (kb-loaded?) #t)

(define (elisp-kb-loaded-p) (if (kb-loaded?) #t #nil))

(define (init-keyboard-stub-registrations)
  "Wire the M0 stub predicate into the elisp symbol table."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((kb-loaded-p ,elisp-kb-loaded-p))))
