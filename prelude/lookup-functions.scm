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

;; Note: Using Guile's built-in string-contains function
;; It returns the index of the substring if found, #f otherwise

;; File path validation helpers
(define (is-absolute-path? path)
  "Check if PATH is an absolute file path."
  (and (> (string-length path) 0)
       (char=? (string-ref path 0) #\/)))

(define (has-directory-traversal? path)
  "Check if PATH contains directory traversal patterns like '../'."
  (or (string-contains path "../")
      (string-contains path "/..")
      (string=? path "..")
      (string-prefix? "../" path)))

;; String preprocessing functions
(define (string-spaces-to-dashes str)
  "Replace all spaces in STR with dashes.
Returns the processed string with spaces converted to dashes."
  (string-map (lambda (c)
                (if (char=? c #\space) #\- c))
              str))

;; String trimming and parsing functions
(define (string-trim-leading-whitespace str)
  "Remove leading whitespace from STR.
Returns the string with leading spaces and tabs removed."
  (let loop ((i 0))
    (cond
      ((>= i (string-length str)) "")
      ((or (char=? (string-ref str i) #\space)
           (char=? (string-ref str i) #\tab))
       (loop (+ i 1)))
      (else (substring str i)))))

;; Number parsing with base support
(define (parse-number-string str base)
  "Parse STR as a number in the given BASE (2-16).
Returns the parsed number or #f if invalid.
Automatically trims leading whitespace."
  (let ((trimmed (string-trim-leading-whitespace str)))
    (if (string=? trimmed "")
        #f
        (string->number trimmed base))))

;; String validation for memory copying
(define (validate-string-for-copying str)
  "Validate that STR is suitable for memory copying operations.
Returns 'valid if safe to copy, 'invalid otherwise."
  (cond
    ((not (string? str)) 'invalid)
    ((= (string-length str) 0) 'invalid)  ; Empty strings might be problematic
    ;; Check for null bytes that could cause issues in C
    ((string-any (lambda (c) (char=? c #\nul)) str) 'invalid)
    (else 'valid)))

;; String preprocessing for symbol creation
(define (prepare-string-for-symbol str)
  "Prepare STR for use as a symbol by converting spaces to dashes.
Returns the processed string suitable for symbol internment."
  (let ((processed (string-spaces-to-dashes str)))
    (if (string=? processed "")
        #f  ; Empty string after processing
        processed)))

;; Filename extension validation
(define (has-file-extension? filename extension)
  "Check if FILENAME has the given EXTENSION.
Both parameters are case-insensitive. Extension should include the dot."
  (and (>= (string-length filename) (string-length extension))
       (string-ci=? extension
                    (substring filename
                               (- (string-length filename) (string-length extension))))))

;; Path component extraction
(define (extract-filename-from-path path)
  "Extract the filename component from a full PATH.
Returns the basename without directory components."
  (let ((last-slash (string-rindex path #\/)))
    (if last-slash
        (substring path (+ last-slash 1))
        path)))

;; String symbol comparison for modifier keys
(define (is-modifier-symbol? symbol-name test-string)
  "Check if SYMBOL-NAME matches TEST-STRING for modifier key comparison.
Returns #t if they match (case-insensitive first 10 chars), #f otherwise."
  (and (>= (string-length symbol-name) (string-length test-string))
       (string-ci=? test-string
                    (substring symbol-name 0 (min 10 (string-length symbol-name))))))

;; Float format validation
(define (validate-float-format-string format-str)
  "Validate that FORMAT-STR is a proper float format string.
Returns 'valid if it starts with % and contains float specifiers, 'invalid otherwise."
  (if (and (> (string-length format-str) 1)
           (char=? (string-ref format-str 0) #\%)
           (or (string-contains format-str "f")
               (string-contains format-str "g")
               (string-contains format-str "e")))
      'valid
      'invalid))

;; Time format string validation
(define (has-time-format-specifiers? format-str)
  "Check if FORMAT-STR contains time formatting specifiers.
Returns #t if it contains %-based time format codes, #f otherwise."
  (and (string-contains format-str "%")
       (or (string-contains format-str "%Y")  ; Year
           (string-contains format-str "%m")  ; Month
           (string-contains format-str "%d")  ; Day
           (string-contains format-str "%H")  ; Hour
           (string-contains format-str "%M")  ; Minute
           (string-contains format-str "%S")  ; Second
           (string-contains format-str "%A")  ; Day name
           (string-contains format-str "%B")))) ; Month name

;; RGB component parsing from color strings
(define (parse-hex-color hex-str)
  "Parse HEX-STR (#RRGGBB format) into RGB components.
Returns (r g b) list or #f if invalid."
  (if (and (= (string-length hex-str) 7)
           (char=? (string-ref hex-str 0) #\#))
      (let ((r-hex (substring hex-str 1 3))
            (g-hex (substring hex-str 3 5))
            (b-hex (substring hex-str 5 7)))
        (let ((r (string->number r-hex 16))
              (g (string->number g-hex 16))
              (b (string->number b-hex 16)))
          (if (and r g b (<= 0 r 255) (<= 0 g 255) (<= 0 b 255))
              (list r g b)
              #f)))
      #f))

;; DOS/Unix filename conversion validation
(define (needs-filename-conversion? filename)
  "Check if FILENAME needs DOS to Unix filename conversion.
Returns #t if it contains backslashes, #f otherwise."
  (string-contains filename "\\"))

;; File encoding validation
(define (is-utf8-filename? filename)
  "Basic check if FILENAME appears to be UTF-8 encoded.
Returns #t if no control characters found, #f otherwise."
  (not (string-any (lambda (c)
                     (let ((code (char->integer c)))
                       (and (< code 32) (not (= code 9)) (not (= code 10)) (not (= code 13)))))
                   filename)))

;; Memory safety validation for string copying
(define (is-safe-for-c-string-copy? str)
  "Check if STR is safe for C string operations.
Returns #t if string contains no null bytes and is reasonable length, #f otherwise."
  (and (> (string-length str) 0)     ; Must be non-empty
       (< (string-length str) 4096)  ; Reasonable length limit
       (not (string-any (lambda (c) (char=? c #\nul)) str))))

;; Network address validation
(define (looks-like-network-address? addr-str)
  "Basic check if ADDR-STR looks like a network address.
Returns #t for IP-like or hostname-like patterns, #f otherwise."
  (or (string-contains addr-str ".")  ; IP or domain
      (string-contains addr-str ":")  ; IPv6 or port
      (string-contains addr-str "localhost")
      (string-contains addr-str "127.0.0.1")))
