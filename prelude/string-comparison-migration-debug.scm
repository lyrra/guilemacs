;; Debug version to isolate character comparison error
(use-modules (ice-9 regex)
             (srfi srfi-1))

;; Add functions gradually to find the problematic one

(define (guile-strcmp str1 str2)
  "Replace strcmp() with Guile string comparison."
  (cond
    ((string=? str1 str2) 0)
    ((string<? str1 str2) -1)
    (else 1)))

(define (keyword-string-equal? str)
  "Check if STR represents a keyword (starts with colon)."
  (and (> (string-length str) 0)
       (char=? (string-ref str 0) #\:)))

(define (special-symbol-string? str)
  "Check if STR is one of the special symbols (nil, t, and, etc.)."
  (member str '("nil" "t" "and" "or" "not" "if" "when" "unless" "cond" "case"
                "lambda" "function" "quote" "backquote" "unquote" "unquote-splicing")))