;;; Guilemacs Lisp - Character Predicates
;;;
;;; Module: (language elisp character-predicates)
;;; Purpose: Character type checking and navigation
;;; Loading: via use-modules in load.scm

(define-module (language elisp character-predicates)
  #:use-module (emacs-elisp runtime)
  #:export (
    elisp-char-alphabetic-p elisp-char-numeric-p
    elisp-char-whitespace-p elisp-char-boundary-p
  ))

;;;
;;; Character Type Checking Functions
;;;

(define (elisp-char-alphabetic-p char)
  "Return t if CHAR is an alphabetic character."
  (if (and (integer? char) (>= char 0) (<= char #x3FFFFF))
      (if (char-alphabetic? (integer->char char)) #t #nil)
      #nil))

(define (elisp-char-numeric-p char)
  "Return t if CHAR is a numeric character."
  (if (and (integer? char) (>= char 0) (<= char #x3FFFFF))
      (if (char-numeric? (integer->char char)) #t #nil)
      #nil))

(define (elisp-char-whitespace-p char)
  "Return t if CHAR is a whitespace character."
  (if (and (integer? char) (>= char 0) (<= char #x3FFFFF))
      (if (char-whitespace? (integer->char char)) #t #nil)
      #nil))

;; Character boundary checking function - safe implementation
(define (elisp-char-boundary-p pos)
  "Return t if POS is at a character boundary in the current buffer.
In UTF-8, this means we're not in the middle of a multi-byte character sequence.
This minimal implementation always returns t since GuilEmacs handles UTF-8 at the character level."
  #t)

;; Register the minimal functions for use from C and Elisp
(set-symbol-function! 'char-alphabetic-p elisp-char-alphabetic-p)
(set-symbol-function! 'char-numeric-p elisp-char-numeric-p)
(set-symbol-function! 'char-whitespace-p elisp-char-whitespace-p)
(set-symbol-function! 'char-boundary-p elisp-char-boundary-p)

;; Export to language elisp emacs module for C access
(let ((elisp-emacs-module (resolve-module '(language elisp emacs) #f)))
  (when elisp-emacs-module
    (module-define! elisp-emacs-module 'char-alphabetic-p elisp-char-alphabetic-p)
    (module-define! elisp-emacs-module 'char-numeric-p elisp-char-numeric-p)
    (module-define! elisp-emacs-module 'char-whitespace-p elisp-char-whitespace-p)
    (module-define! elisp-emacs-module 'char-boundary-p elisp-char-boundary-p)))
