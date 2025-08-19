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

;; File path validation helpers (see more complete versions below in SSDATA hoisting section)

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

;; Filename extension validation (see more complete version below in SSDATA hoisting section)

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
  "Check if SYMBOL-NAME starts with TEST-STRING for modifier key comparison.
Returns #t if symbol name starts with test string (case-insensitive), #f otherwise."
  (and (>= (string-length symbol-name) (string-length test-string))
       (string-ci=? test-string
                    (substring symbol-name 0 (string-length test-string)))))

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

;; Path/Filename Operations for SSDATA hoisting

;; Check if path is absolute (cross-platform)
(define (is-absolute-path? path)
  "Check if PATH is an absolute path (cross-platform).
Returns #t for absolute paths, #f for relative ones."
  (cond
    ;; Empty path is not absolute
    ((= (string-length path) 0) #f)
    ;; Unix-style absolute path (starts with /)
    ((char=? (string-ref path 0) #\/) #t)
    ;; Windows-style absolute path (C:\ or C:/)
    ((and (>= (string-length path) 3)
          (char-alphabetic? (string-ref path 0))
          (char=? (string-ref path 1) #\:)
          (or (char=? (string-ref path 2) #\\)
              (char=? (string-ref path 2) #\/))) #t)
    ;; UNC path (\\server\share)
    ((and (>= (string-length path) 2)
          (char=? (string-ref path 0) #\\)
          (char=? (string-ref path 1) #\\)) #t)
    ;; Not absolute
    (else #f)))

;; Check if path ends with directory separator
(define (ends-with-directory-separator? path)
  "Check if PATH ends with a directory separator (/ or \\).
Returns #t if path ends with separator, #f otherwise."
  (if (= (string-length path) 0)
      #f
      (let ((last-char (string-ref path (- (string-length path) 1))))
        (or (char=? last-char #\/)
            (char=? last-char #\\)))))

;; Normalize path separators (convert / to \ on Windows)
(define (normalize-path-separators path)
  "Normalize PATH by converting forward slashes to backslashes.
Returns the normalized path string."
  (string-map (lambda (c)
                (if (char=? c #\/) #\\ c))
              path))

;; Check if string is empty
(define (string-empty? str)
  "Check if STR is empty (zero length).
Returns #t if empty, #f otherwise."
  (= (string-length str) 0))

;; Check if path has directory traversal patterns
(define (has-directory-traversal? path)
  "Check if PATH contains directory traversal patterns like .. or ./.
Returns #t if potentially dangerous patterns found, #f otherwise."
  (or (string-contains path "..")
      (string-contains path "./")
      (string-contains path ".\\")))

;; Extract file extension from path
(define (get-file-extension path)
  "Extract the file extension from PATH.
Returns the extension (including dot) or empty string if none."
  (let ((last-dot (string-rindex path #\.))
        (last-slash (or (string-rindex path #\/)
                       (string-rindex path #\\)
                       -1)))
    (if (and last-dot (> last-dot last-slash))
        (substring path last-dot)
        "")))

;; Check if path starts with specific prefix
(define (path-starts-with? path prefix)
  "Check if PATH starts with PREFIX (case-insensitive).
Returns #t if path starts with prefix, #f otherwise."
  (and (>= (string-length path) (string-length prefix))
       (string-ci=? prefix
                    (substring path 0 (string-length prefix)))))

;; Simple String Validation Operations for SSDATA hoisting

;; Check if string has exactly one character
(define (string-single-char? str)
  "Check if STR contains exactly one character.
Returns #t if string length is 1, #f otherwise."
  (= (string-length str) 1))

;; Check if string starts with space character
(define (string-starts-with-space? str)
  "Check if STR starts with a space character.
Returns #t if first character is space, #f otherwise."
  (and (> (string-length str) 0)
       (char=? (string-ref str 0) #\space)))

;; Check if string contains only ASCII characters
(define (string-ascii-only? str)
  "Check if STR contains only ASCII characters (0-127).
Returns #t if all characters are ASCII, #f otherwise."
  (string-every (lambda (c)
                  (< (char->integer c) 128))
                str))

;; Check if string is a valid symbol name
(define (valid-symbol-name? str)
  "Check if STR is a valid Lisp symbol name.
Returns #t if valid, #f otherwise."
  (and (> (string-length str) 0)
       ;; Cannot start with digit
       (not (char-numeric? (string-ref str 0)))
       ;; Must contain only valid symbol characters
       (string-every (lambda (c)
                       (or (char-alphabetic? c)
                           (char-numeric? c)
                           (char=? c #\-)
                           (char=? c #\_)
                           (char=? c #\?)
                           (char=? c #\!)
                           (char=? c #\*)))
                     str)))

;; Check if string looks like a number
(define (string-numeric? str)
  "Check if STR looks like a numeric string.
Returns #t if it can be parsed as a number, #f otherwise."
  (catch #t
    (lambda ()
      (string->number str))
    (lambda (key . args)
      #f)))

;; Check if string contains special characters that need escaping
(define (string-needs-escaping? str)
  "Check if STR contains characters that typically need escaping.
Returns #t if contains quotes, backslashes, or control chars, #f otherwise."
  (string-any (lambda (c)
                (or (char=? c #\")
                    (char=? c #\\)
                    (char=? c #\')
                    (< (char->integer c) 32)))
              str))

;; Buffer name validation
(define (special-buffer-name? buffer-name)
  "Check if BUFFER-NAME represents a special/internal buffer.
Returns #t for special buffers (starting with space or star), #f otherwise."
  (cond
    ;; Empty name
    ((= (string-length buffer-name) 0) #t)
    ;; Names starting with space (hidden buffers)
    ((char=? (string-ref buffer-name 0) #\space) #t)
    ;; Names starting and ending with asterisks (special buffers)
    ((and (>= (string-length buffer-name) 2)
          (char=? (string-ref buffer-name 0) #\*)
          (char=? (string-ref buffer-name (- (string-length buffer-name) 1)) #\*)) #t)
    ;; Regular buffer
    (else #f)))

;; Simple case-insensitive string comparison
(define (string-equal-ignore-case? str1 str2)
  "Case-insensitive string comparison.
Returns #t if strings are equal ignoring case, #f otherwise."
  (string-ci=? str1 str2))

;; Check if string starts with specific character
(define (string-starts-with-char? str char-or-int)
  "Check if STR starts with specific CHAR-OR-INT.
CHAR-OR-INT can be either a character or an integer character code.
Returns #t if first character matches, #f otherwise."
  (and (> (string-length str) 0)
       (let ((char (if (integer? char-or-int)
                       (integer->char char-or-int)
                       char-or-int)))
         (char=? (string-ref str 0) char))))

;; Check if string ends with specific character
(define (string-ends-with-char? str char-or-int)
  "Check if STR ends with specific CHAR-OR-INT.
CHAR-OR-INT can be either a character or an integer character code.
Returns #t if last character matches, #f otherwise."
  (and (> (string-length str) 0)
       (let ((char (if (integer? char-or-int)
                       (integer->char char-or-int)
                       char-or-int)))
         (char=? (string-ref str (- (string-length str) 1)) char))))

;; Check if string contains only whitespace
(define (string-whitespace-only? str)
  "Check if STR contains only whitespace characters.
Returns #t if all characters are whitespace, #f otherwise."
  (string-every char-whitespace? str))

;; Check if string is a valid identifier
(define (valid-identifier? str)
  "Check if STR is a valid programming identifier.
Returns #t if valid (starts with letter/underscore, contains alphanumeric), #f otherwise."
  (and (> (string-length str) 0)
       ;; Must start with letter or underscore
       (or (char-alphabetic? (string-ref str 0))
           (char=? (string-ref str 0) #\_))
       ;; Rest must be alphanumeric or underscore
       (string-every (lambda (c)
                       (or (char-alphabetic? c)
                           (char-numeric? c)
                           (char=? c #\_)))
                     str)))

;; File Extension and Type Operations for SSDATA hoisting

;; Check if filename has specific extension (case-insensitive)
(define (has-file-extension? filename extension)
  "Check if FILENAME ends with EXTENSION (case-insensitive).
Returns #t if filename has the extension, #f otherwise."
  (let ((ext-len (string-length extension))
        (name-len (string-length filename)))
    (and (>= name-len ext-len)
         (string-ci=? extension
                     (substring filename (- name-len ext-len))))))

;; Check if filename is a source code file
(define (source-code-file? filename)
  "Check if FILENAME appears to be a source code file.
Returns #t for common source file extensions, #f otherwise."
  (or (has-file-extension? filename ".c")
      (has-file-extension? filename ".h")
      (has-file-extension? filename ".el")
      (has-file-extension? filename ".scm")
      (has-file-extension? filename ".lisp")
      (has-file-extension? filename ".py")
      (has-file-extension? filename ".js")
      (has-file-extension? filename ".cpp")
      (has-file-extension? filename ".hpp")))

;; Check if filename is an image file
(define (image-file? filename)
  "Check if FILENAME appears to be an image file.
Returns #t for common image extensions, #f otherwise."
  (or (has-file-extension? filename ".png")
      (has-file-extension? filename ".jpg")
      (has-file-extension? filename ".jpeg")
      (has-file-extension? filename ".gif")
      (has-file-extension? filename ".bmp")
      (has-file-extension? filename ".svg")
      (has-file-extension? filename ".tiff")
      (has-file-extension? filename ".webp")))

;; Check if filename is a data/config file
(define (config-file? filename)
  "Check if FILENAME appears to be a configuration file.
Returns #t for common config extensions, #f otherwise."
  (or (has-file-extension? filename ".json")
      (has-file-extension? filename ".xml")
      (has-file-extension? filename ".yaml")
      (has-file-extension? filename ".yml")
      (has-file-extension? filename ".toml")
      (has-file-extension? filename ".ini")
      (has-file-extension? filename ".conf")))

;; Extract file extension including the dot
(define (extract-file-extension filename)
  "Extract file extension from FILENAME including the dot.
Returns the extension or empty string if none."
  (let ((last-dot (string-rindex filename #\.))
        (last-slash (or (string-rindex filename #\/)
                       (string-rindex filename #\\)
                       -1)))
    (if (and last-dot (> last-dot last-slash))
        (substring filename last-dot)
        "")))

;; Font and Color Validation Operations for SSDATA hoisting

;; Check if string looks like a hex color
(define (hex-color-string? str)
  "Check if STR looks like a hex color (#RGB, #RRGGBB, etc.).
Returns #t if valid hex color format, #f otherwise."
  (and (> (string-length str) 1)
       (char=? (string-ref str 0) #\#)
       (let ((hex-part (substring str 1)))
         (and (> (string-length hex-part) 0)
              ;; Valid lengths: 3, 6, 8, 12 (RGB, RRGGBB, RRGGBBAA, RRRRGGGGBBBB)
              (member (string-length hex-part) '(3 6 8 12))
              ;; All characters must be hex digits
              (string-every (lambda (c)
                              (or (char<=? #\0 c #\9)
                                  (char<=? #\a (char-downcase c) #\f)))
                            hex-part)))))

;; Check if string looks like RGB color function
(define (rgb-color-string? str)
  "Check if STR looks like rgb() or rgba() color function.
Returns #t if valid RGB format, #f otherwise."
  (and (> (string-length str) 4)
       (or (string-prefix-ci? "rgb(" str)
           (string-prefix-ci? "rgba(" str))
       (string-suffix? ")" str)))

;; Check if string is a named color
(define (named-color? color-name)
  "Check if COLOR-NAME is a known named color.
Returns #t for common HTML/CSS color names, #f otherwise."
  (member (string-downcase color-name)
          '("red" "green" "blue" "white" "black" "yellow" "cyan" "magenta"
            "orange" "purple" "pink" "brown" "gray" "grey" "silver" "gold"
            "navy" "maroon" "olive" "lime" "aqua" "teal" "fuchsia" "violet"
            "indigo" "crimson" "salmon" "coral" "khaki" "plum" "orchid"
            "chocolate" "sienna" "peru" "tan" "wheat" "beige" "ivory")))

;; Validate XLFD (X Logical Font Description) font name
(define (valid-xlfd-font-name? font-name)
  "Check if FONT-NAME is a valid XLFD format.
Returns #t if valid XLFD format, #f otherwise."
  (and (> (string-length font-name) 0)
       ;; XLFD starts with dash and has exactly 14 dashes total
       (char=? (string-ref font-name 0) #\-)
       (= (string-count font-name #\-) 14)
       ;; Must not be too short or too long
       (> (string-length font-name) 20)
       (< (string-length font-name) 200)))

;; Check if string looks like a font family name
(define (font-family-name? name)
  "Check if NAME looks like a font family name.
Returns #t if reasonable font name, #f otherwise."
  (and (> (string-length name) 0)
       (< (string-length name) 50)
       ;; Must contain letters
       (string-any char-alphabetic? name)
       ;; Common font name patterns
       (or (string-any char-alphabetic? name)
           (string-contains name " ")
           (string-contains name "-"))))

;; Network and URL Operations for SSDATA hoisting

;; Check if string looks like a URL
(define (url-string? str)
  "Check if STR looks like a URL.
Returns #t if URL-like format, #f otherwise."
  (and (> (string-length str) 4)
       (or (string-prefix-ci? "http://" str)
           (string-prefix-ci? "https://" str)
           (string-prefix-ci? "ftp://" str)
           (string-prefix-ci? "file://" str)
           (string-prefix-ci? "mailto:" str))))

;; Check if string looks like an email address
(define (email-address? str)
  "Check if STR looks like an email address.
Returns #t if email-like format, #f otherwise."
  (and (> (string-length str) 3)
       (string-contains str "@")
       (string-contains str ".")
       ;; Basic validation - at least one char before @, domain after
       (let ((at-pos (string-index str #\@)))
         (and at-pos
              (> at-pos 0)
              (< at-pos (- (string-length str) 2))
              (string-contains (substring str (+ at-pos 1)) ".")))))

;; Check if string looks like an IP address
(define (ip-address? str)
  "Check if STR looks like an IPv4 address.
Returns #t if IP-like format, #f otherwise."
  (and (> (string-length str) 6)  ; minimum: 1.1.1.1
       (< (string-length str) 16)  ; maximum: 255.255.255.255
       (= (string-count str #\.) 3)
       ;; Split and validate each octet
       (let ((parts (string-split str #\.)))
         (and (= (length parts) 4)
              (let loop ((parts parts))
                (cond
                  ((null? parts) #t)
                  ((let ((part (car parts)))
                     (and (> (string-length part) 0)
                          (< (string-length part) 4)
                          (string-every char-numeric? part)
                          (let ((num (string->number part)))
                            (and num (>= num 0) (<= num 255)))))
                   (loop (cdr parts)))
                  (else #f)))))))

;; Registry to script mapping lookup for font handling
;; Looks up a registry string in the ns_reg_to_script mapping
(define (lookup-registry-to-script reg-to-script-alist registry-str)
  "Look up REGISTRY-STR in REG-TO-SCRIPT-ALIST to find matching script.
The alist contains (registry-pattern . script-symbol) pairs.
Returns the script symbol if found, #f otherwise.
Matches if registry string starts with the pattern."
  (let loop ((alist reg-to-script-alist))
    (cond
      ((null? alist) #f)
      ((and (pair? (car alist))
            (string? (caar alist))
            (string? registry-str)
            ;; Check if registry-str starts with the pattern (like strncmp)
            (>= (string-length registry-str) (string-length (caar alist)))
            (string=? (caar alist)
                     (substring registry-str 0 (string-length (caar alist)))))
       (cdar alist))  ; return script symbol
      (else (loop (cdr alist))))))

;; File path operations for SSDATA migration
;; These functions replace SSDATA usage in fileio.c

;; Check if a file path is absolute
(define (file-path-absolute-p path-str)
  "Check if PATH-STR represents an absolute file path.
This replaces SSDATA usage in file_name_absolute_p.
Returns #t for absolute paths, #f for relative paths."
  (if (or (not (string? path-str))
          (= (string-length path-str) 0))
      #f
      (let ((first-char (string-ref path-str 0)))
        (or (char=? first-char #\/)           ; Unix absolute path
            (char=? first-char #\~)           ; Home directory
            (and (> (string-length path-str) 2)  ; Windows drive letter
                 (char-alphabetic? first-char)
                 (char=? (string-ref path-str 1) #\:)
                 (or (char=? (string-ref path-str 2) #\/)
                     (char=? (string-ref path-str 2) #\\)))))))

;; Extract directory component from file path
(define (file-path-directory path-str)
  "Extract directory component from PATH-STR.
This replaces SSDATA usage in file_name_directory function.
Returns directory path or empty string if no directory."
  (if (or (not (string? path-str))
          (= (string-length path-str) 0))
      ""
      (let ((last-sep -1))
        ;; Find last directory separator
        (do ((i (- (string-length path-str) 1) (- i 1)))
            ((or (< i 0) (>= last-sep 0)))
          (let ((c (string-ref path-str i)))
            (when (or (char=? c #\/) (char=? c #\\))
              (set! last-sep i))))
        (if (< last-sep 0)
            ""  ; No directory separator found
            (substring path-str 0 (+ last-sep 1))))))

;; Extract filename component from file path
(define (file-path-nondirectory path-str)
  "Extract filename component from PATH-STR.
This replaces SSDATA usage in file_name_nondirectory function.
Returns filename without directory path."
  (if (or (not (string? path-str))
          (= (string-length path-str) 0))
      ""
      (let ((last-sep -1))
        ;; Find last directory separator
        (do ((i (- (string-length path-str) 1) (- i 1)))
            ((or (< i 0) (>= last-sep 0)))
          (let ((c (string-ref path-str i)))
            (when (or (char=? c #\/) (char=? c #\\))
              (set! last-sep i))))
        (if (< last-sep 0)
            path-str  ; No separator, entire string is filename
            (substring path-str (+ last-sep 1))))))

;; Validate file path for safety (detect directory traversal, etc.)
(define (file-path-safe-p path-str)
  "Check if PATH-STR is safe from directory traversal attacks.
This replaces SSDATA usage in file path validation.
Returns #t if safe, #f if potentially dangerous."
  (if (or (not (string? path-str))
          (= (string-length path-str) 0))
      #f
      (not (or (string-contains path-str "../")
               (string-contains path-str "..\\")
               (string-suffix? "/.." path-str)
               (string-suffix? "\\.." path-str)
               (string=? ".." path-str)))))

;; String operations without properties for SSDATA migration
;; Pure substring operation that replaces SSDATA usage in substring-no-properties
(define (substring-no-properties-scheme str start end)
  "Extract substring from STR between START and END indices.
This is a pure Scheme implementation that replaces SSDATA usage.
Returns the substring without any text properties.
Handles negative indices and boundary conditions."
  (if (or (not (string? str))
          (= (string-length str) 0))
      ""
      (let* ((len (string-length str))
             ;; Handle negative indices and defaults
             (actual-start (cond
                            ((not start) 0)
                            ((< start 0) (max 0 (+ len start)))
                            (else (min start len))))
             (actual-end (cond
                          ((not end) len)
                          ((< end 0) (max 0 (+ len end)))
                          (else (min end len))))
             ;; Ensure start <= end
             (final-start (min actual-start actual-end))
             (final-end (max actual-start actual-end)))
        (if (>= final-start final-end)
            ""
            (substring str final-start final-end)))))

;; Font name parsing for size extraction
;; Parses font names like "Foobar-123" to extract family and size
(define (parse-font-name-with-size font-name-str current-size)
  "Parse FONT-NAME-STR to extract family name and size.
Looks for pattern 'FontFamily-Size' where Size is a number.
CURRENT-SIZE is the currently parsed size for validation.
Returns (family-name . parsed-size) if successful, #f if no size found.
This replaces SSDATA usage in font.c for font name parsing."
  (if (or (not (string? font-name-str))
          (= (string-length font-name-str) 0)) ; handle empty string
      #f
      (let ((dash-pos (string-rindex font-name-str #\-)))
        (if (and dash-pos
                 (> dash-pos 0) ; dash not at start
                 (< dash-pos (- (string-length font-name-str) 1))) ; dash not at end
            (let* ((after-dash (substring font-name-str (+ dash-pos 1)))
                   (family-part (substring font-name-str 0 dash-pos)))
              (if (and (> (string-length after-dash) 0)
                       (char-numeric? (string-ref after-dash 0))) ; first char is digit
                  (let ((parsed-size (string->number after-dash)))
                    (if (and parsed-size
                             (> parsed-size 0)
                             ;; Validate against current size if provided
                             (or (not current-size)
                                 (= parsed-size current-size)))
                        (cons family-part parsed-size)
                        #f))
                  #f))
            #f))))
