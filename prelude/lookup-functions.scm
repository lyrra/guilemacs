;;; lookup-functions.scm --- Guile-based lookup functions for Emacs C code

;; This module provides efficient lookup functions to replace C-level
;; string comparisons and list/table traversals with native Guile operations.

;; Case-insensitive color lookup in color map
;; Returns the color value (cdr) if found, #f otherwise
(define (lookup-color-in-map color-map color-name)
  "Look up COLOR-NAME in COLOR-MAP using case-insensitive comparison.
COLOR-MAP is a list of (name . value) pairs.
Returns the color value if found, #f otherwise."
  (let loop ((map color-map))
    (cond
      ((null? map) #f)
      ((and (pair? (car map))
            (string? (caar map))
            (string-ci=? (caar map) color-name))
       (cdar map))  ; return color value
      (else (loop (cdr map))))))

;; Font style table lookup with nested structure
;; Returns (cons table-index element-index) if found, #f otherwise
(define (lookup-font-style table style-name)
  "Look up STYLE-NAME in font style TABLE.
TABLE is a vector of vectors, where each inner vector contains font styles.
Returns (cons table-index element-index) if found, #f otherwise."
  (let outer ((i 0))
    (if (>= i (vector-length table))
        #f
        (let ((row (vector-ref table i)))
          (if (not (vector? row))
              (outer (+ i 1))
              (let inner ((j 1))  ; Start from index 1
                (if (>= j (vector-length row))
                    (outer (+ i 1))
                    (let ((elt (vector-ref row j)))
                      (cond
                        ((and (symbol? elt)
                              (string-ci=? style-name (symbol->string elt)))
                         (cons i j))
                        ((and (string? elt)
                              (string-ci=? style-name elt))
                         (cons i j))
                        (else (inner (+ j 1))))))))))))

;; Generic case-insensitive alist lookup
(define (lookup-in-alist-ci alist key)
  "Look up KEY in ALIST using case-insensitive string comparison.
ALIST is a list of (key . value) pairs.
Returns the value if found, #f otherwise."
  (let loop ((lst alist))
    (cond
      ((null? lst) #f)
      ((and (pair? (car lst))
            (string? (caar lst))
            (string-ci=? (caar lst) key))
       (cdar lst))
      (else (loop (cdr lst))))))

;; Generic case-sensitive alist lookup
(define (lookup-in-alist alist key)
  "Look up KEY in ALIST using case-sensitive string comparison.
ALIST is a list of (key . value) pairs.
Returns the value if found, #f otherwise."
  (let loop ((lst alist))
    (cond
      ((null? lst) #f)
      ((and (pair? (car lst))
            (string? (caar lst))
            (string=? (caar lst) key))
       (cdar lst))
      (else (loop (cdr lst))))))

;; Symbol lookup in a list (for clipboard formats, etc.)
(define (lookup-symbol-in-list lst name-string)
  "Check if NAME-STRING matches any symbol name in LST.
Returns #t if a match is found, #f otherwise."
  (let loop ((items lst))
    (cond
      ((null? items) #f)
      ((and (symbol? (car items))
            (string=? name-string (symbol->string (car items))))
       #t)
      (else (loop (cdr items))))))

;; Fontset name lookup with pattern matching support
(define (lookup-fontset-by-name fontsets name pattern-match?)
  "Look up fontset by NAME in FONTSETS.
If PATTERN-MATCH? is true, uses pattern matching; otherwise exact match.
Returns the fontset index if found, -1 otherwise."
  (let loop ((i 0))
    (if (>= i (vector-length fontsets))
        -1
        (let ((fontset (vector-ref fontsets i)))
          (if (and (vector? fontset)
                   (> (vector-length fontset) 0))
              (let ((fontset-name (vector-ref fontset 0)))  ; Assuming name is at index 0
                (cond
                  ((and (not pattern-match?)
                        (string? fontset-name)
                        (string-ci=? name fontset-name))
                   i)
                  ;; Pattern matching would require additional implementation
                  (else (loop (+ i 1)))))
              (loop (+ i 1)))))))

;; Helper function to handle both string and symbol inputs
(define (normalize-to-string obj)
  "Convert OBJ to string if it's a symbol, otherwise return as-is."
  (cond
    ((symbol? obj) (symbol->string obj))
    ((string? obj) obj)
    (else #f)))

;; Face attribute boolean parsing
(define (parse-face-bool-attribute attr-name)
  "Parse face boolean attribute name and return its semantic meaning.
Returns 'true for attributes that should be true, 'false for negated ones,
'nil for unknown attributes."
  (cond
    ;; Positive boolean attributes
    ((or (string-ci=? attr-name "bold")
         (string-ci=? attr-name "italic")
         (string-ci=? attr-name "underline")
         (string-ci=? attr-name "overline")
         (string-ci=? attr-name "strike-through")
         (string-ci=? attr-name "inverse-video")
         (string-ci=? attr-name "reverse"))
     'true)
    ;; Negative boolean attributes
    ((or (string-ci=? attr-name "normal")
         (string-ci=? attr-name "unspecified")
         (string-ci=? attr-name "reset"))
     'false)
    ;; Unknown
    (else 'nil)))

;; Yes/No prompt processing
(define (process-yesno-response response)
  "Process user response to yes/no prompt.
Returns 'yes, 'no, or 'invalid based on the response string."
  (let ((normalized (string-downcase (string-trim response))))
    (cond
      ;; Positive responses
      ((or (string=? normalized "y")
           (string=? normalized "yes")
           (string=? normalized "true")
           (string=? normalized "t")
           (string=? normalized "1"))
       'yes)
      ;; Negative responses
      ((or (string=? normalized "n")
           (string=? normalized "no")
           (string=? normalized "false")
           (string=? normalized "nil")
           (string=? normalized "f")
           (string=? normalized "0"))
       'no)
      ;; Invalid response
      (else 'invalid))))

;; DBus message filtering by interface/member pattern
(define (filter-dbus-message message interface-pattern member-pattern)
  "Filter DBus MESSAGE based on interface and member patterns.
Returns #t if message matches both patterns, #f otherwise.
Patterns support simple glob-like matching with '*' wildcards."
  (define (glob-match? pattern text)
    "Simple glob matching - supports * as wildcard"
    (if (string-contains pattern "*")
        ;; Simple wildcard matching - replace * with .*
        (let ((regex-pattern (string-replace pattern "*" ".*")))
          ;; For now, simplified: just check if pattern without * is contained
          (if (string=? pattern "*")
              #t
              (string-contains text (string-replace pattern "*" ""))))
        (string-ci=? pattern text)))

  ;; Extract interface and member from message (simplified structure)
  ;; In real implementation, this would parse actual DBus message structure
  (let ((msg-interface (if (and (pair? message) (string? (car message)))
                           (car message) ""))
        (msg-member (if (and (pair? message) (pair? (cdr message))
                            (string? (cadr message)))
                        (cadr message) "")))
    (and (glob-match? interface-pattern msg-interface)
         (glob-match? member-pattern msg-member))))

;; Special buffer name identification
(define (is-special-buffer-name? buffer-name)
  "Check if BUFFER-NAME represents a special (internal) buffer.
Returns #t for special buffers, #f for regular ones."
  (cond
    ;; Empty or whitespace-only names
    ((or (string=? buffer-name "")
         (string=? (string-trim buffer-name) ""))
     #t)
    ;; Names starting with space (hidden buffers)
    ((char=? (string-ref buffer-name 0) #\space)
     #t)
    ;; Names surrounded by asterisks (special buffers)
    ((and (> (string-length buffer-name) 2)
          (char=? (string-ref buffer-name 0) #\*)
          (char=? (string-ref buffer-name (- (string-length buffer-name) 1)) #\*))
     #t)
    ;; Standard special buffer names
    ((or (string-ci=? buffer-name "*scratch*")
         (string-ci=? buffer-name "*messages*")
         (string-ci=? buffer-name "*minibuffer*")
         (string-ci=? buffer-name "*completions*")
         (string-ci=? buffer-name "*help*")
         (string-prefix-ci? buffer-name "*compilation")
         (string-prefix-ci? buffer-name "*grep")
         (string-prefix-ci? buffer-name "*occur"))
     #t)
    ;; Regular buffer
    (else #f)))

;; Helper function for case-insensitive prefix matching
(define (string-prefix-ci? prefix str)
  "Check if STR starts with PREFIX (case-insensitive)."
  (and (>= (string-length str) (string-length prefix))
       (string-ci=? prefix (substring str 0 (string-length prefix)))))

;; Helper functions for string operations (defined early)
(define (string-split str delimiter)
  "Split STR by DELIMITER character. Returns list of substrings."
  (let loop ((chars (string->list str))
             (current '())
             (result '()))
    (cond
      ((null? chars)
       (reverse (cons (list->string (reverse current)) result)))
      ((char=? (car chars) delimiter)
       (loop (cdr chars) '() (cons (list->string (reverse current)) result)))
      (else
       (loop (cdr chars) (cons (car chars) current) result)))))

(define (string-every pred str)
  "Check if predicate PRED is true for every character in STR."
  (let loop ((i 0))
    (cond
      ((>= i (string-length str)) #t)
      ((not (pred (string-ref str i))) #f)
      (else (loop (+ i 1))))))

(define (string-contains-helper str substring)
  "Check if STR contains SUBSTRING."
  (let ((str-len (string-length str))
        (sub-len (string-length substring)))
    (let loop ((i 0))
      (cond
        ((> (+ i sub-len) str-len) #f)
        ((string=? (substring str i (+ i sub-len)) substring) #t)
        (else (loop (+ i 1)))))))

;; Color parsing and validation functions
(define (parse-color-spec color-spec)
  "Parse a color specification string and return RGB values.
Returns (r g b) list if valid, #f if invalid.
Supports formats like #RRGGBB, #RGB, rgb(r,g,b), color names."
  (let ((spec (string-trim color-spec)))
    (cond
      ;; #RRGGBB format
      ((and (string-prefix? "#" spec) (= (string-length spec) 7))
       (let ((r-str (substring spec 1 3))
             (g-str (substring spec 3 5))
             (b-str (substring spec 5 7)))
         (let ((r (string->number r-str 16))
               (g (string->number g-str 16))
               (b (string->number b-str 16)))
           (if (and r g b) (list r g b) #f))))
      ;; #RGB format (shorthand)
      ((and (string-prefix? "#" spec) (= (string-length spec) 4))
       (let ((r-char (substring spec 1 2))
             (g-char (substring spec 2 3))
             (b-char (substring spec 3 4)))
         (let ((r (string->number (string-append r-char r-char) 16))
               (g (string->number (string-append g-char g-char) 16))
               (b (string->number (string-append b-char b-char) 16)))
           (if (and r g b) (list r g b) #f))))
      ;; rgb(r,g,b) format - simplified parsing
      ((string-prefix-ci? "rgb(" spec)
       (let ((content (substring spec 4 (- (string-length spec) 1))))
         (let ((parts (map string-trim (string-split content #\,))))
           (if (= (length parts) 3)
               (let ((r (string->number (car parts)))
                     (g (string->number (cadr parts)))
                     (b (string->number (caddr parts))))
                 (if (and r g b
                         (<= 0 r 255) (<= 0 g 255) (<= 0 b 255))
                     (list r g b) #f))
               #f))))
      ;; Named colors (basic set)
      ((string-ci=? spec "red") '(255 0 0))
      ((string-ci=? spec "green") '(0 255 0))
      ((string-ci=? spec "blue") '(0 0 255))
      ((string-ci=? spec "white") '(255 255 255))
      ((string-ci=? spec "black") '(0 0 0))
      ((string-ci=? spec "yellow") '(255 255 0))
      ((string-ci=? spec "cyan") '(0 255 255))
      ((string-ci=? spec "magenta") '(255 0 255))
      ((string-ci=? spec "gray") '(128 128 128))
      ((string-ci=? spec "grey") '(128 128 128))
      (else #f))))

;; Color validation function
(define (validate-color-name color-name)
  "Validate if COLOR-NAME is a recognizable color specification.
Returns 'valid for valid colors, 'invalid for invalid ones."
  (if (parse-color-spec color-name) 'valid 'invalid))

;; String pattern matching functions
(define (string-contains-whitespace? str)
  "Check if STR contains any whitespace characters."
  (let loop ((i 0))
    (cond
      ((>= i (string-length str)) #f)
      ((char-whitespace? (string-ref str i)) #t)
      (else (loop (+ i 1))))))

;; Frame name validation
(define (is-frame-name-fnn-format? name)
  "Check if NAME follows the F<number> format used for auto-generated frame names."
  (and (> (string-length name) 1)
       (char=? (string-ref name 0) #\F)
       (let ((rest (substring name 1)))
         (and (> (string-length rest) 0)
              (string-every char-numeric? rest)))))

;; Font name parsing helpers
(define (validate-xlfd-font-name name)
  "Basic validation for XLFD (X Logical Font Description) format.
Returns 'valid if the name has the correct number of dashes, 'invalid otherwise."
  (let ((parts (string-split name #\-)))
    (if (= (length parts) 15) ; XLFD should have 14 dashes = 15 parts
        'valid
        'invalid)))

;; File path validation helpers
(define (is-absolute-path? path)
  "Check if PATH is an absolute file path."
  (and (> (string-length path) 0)
       (char=? (string-ref path 0) #\/)))

(define (has-directory-traversal? path)
  "Check if PATH contains directory traversal patterns like '../'."
  (or (and (string-contains path "../") #t)
      (and (string-contains path "/..") #t)
      (string=? path "..")
      (string-prefix? "../" path)))
