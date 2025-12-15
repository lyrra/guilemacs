;;; Guilemacs Lisp
;;;
;;; Character Predicates
;;;
;;; Module: (language elisp runtime characters)
;;; Purpose: Character type checking and navigation
;;; Loaded into: (language elisp runtime) via primitive-load
;;;
;;; EXPORTS (4 functions):
;;;   Type checking: char-alphabetic-p, char-numeric-p
;;;   Whitespace: char-whitespace-p
;;;   Boundaries: char-boundary-p
;;;
;;; Minimal safe implementation that doesn't depend on buffer operations.
;;; Addresses UTF-8 migration requirements for character type checking.
;;;
;;; NOTE: Module declaration commented out for Phase 1. Will be enabled
;;;       when load.scm is updated to use use-modules.
;;;
;;; (define-module (language elisp runtime characters)
;;;   #:use-module (language elisp runtime)
;;;   #:export (...))

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