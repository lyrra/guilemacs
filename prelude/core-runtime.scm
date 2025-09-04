;; Core runtime functions needed before the main prelude can load
;; This provides the minimal set of functions that C code expects to find
;; in the (language elisp runtime) module

;; Ensure we're in the correct module
(define-module (language elisp runtime)
  #:export (symbol-desc
            symbol-function
            set-symbol-function!
            symbol-plist
            set-symbol-plist!
            symbol-name
            unbound
            eval-elisp
            emacs!))

;; Symbol system - basic implementation
(define unbound 'unbound)

(define (symbol-desc sym)
  "Get symbol descriptor - simplified implementation"
  sym)

(define symbol-table (make-hash-table))

(define (symbol-function sym)
  "Get the function binding of a symbol"
  (hash-ref symbol-table sym unbound))

(define (set-symbol-function! sym func)
  "Set the function binding of a symbol"
  (hash-set! symbol-table sym func))

;; Property list system - basic implementation
(define plist-table (make-hash-table))

(define (symbol-plist sym)
  "Get the property list of a symbol"
  (hash-ref plist-table sym '()))

(define (set-symbol-plist! sym plist)
  "Set the property list of a symbol"
  (hash-set! plist-table sym plist))

(define (symbol-name sym)
  "Get the name of a symbol as a string"
  (if (symbol? sym)
      (symbol->string sym)
      ""))

(define (eval-elisp expr)
  "Evaluate an Elisp expression - basic implementation"
  (eval expr (current-module)))

(define (emacs! . args)
  "Main emacs entry point - placeholder"
  #t)

;; Additional minimal arithmetic functions that are referenced
(define (elisp-+ . args)
  "Addition function"
  (apply + args))

(define (elisp-* . args)
  "Multiplication function"
  (apply * args))

(define (elisp-char-to-string char)
  "Convert character to string"
  (string (integer->char char)))

(define (elisp-mod a b)
  "Modulo function"
  (modulo a b))

(define (elisp-string . chars)
  "Create string from characters"
  (list->string (map integer->char chars)))