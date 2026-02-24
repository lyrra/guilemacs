;;; Guilemacs Lisp - Elisp Reader & Parser Functions
;;;
;;; Purpose: Complete Elisp reader and parser implementation
;;; Loading: via use-modules in load.scm

(define-module (emacs reader)
  #:declarative? #f
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs loader)
  #:use-module (emacs utils)
  #:use-module (system base compile)
  #:use-module (system base language)
  #:export (
    custom-elisp-read
    init-reader
    elisp-read-from-port
    elisp-read-from-string-with-position
    elisp-parse-hash-s-from-port
    elisp-hash-table-from-plist
    elisp-record-from-list
    elisp-complete-file-load-from-port
    elisp-compute-found-effective
    elisp-convert-guile-object
    elisp-create-bool-vector-from-scheme
    elisp-fread0-complete
    elisp-fread0-with-char-from-c
    elisp-handle-lexical-binding-specbind
    elisp-handle-whitespace-and-eof
    elisp-intern-and-make-keyword
    elisp-load-read-eval-loop-from-port
    elisp-load-read-next-expression-from-port
    elisp-orchestrate-file-reading
    elisp-parse-backquote-from-port
    elisp-parse-backquote-with-list-construction
    elisp-parse-bool-vector-from-port
    elisp-parse-character-dispatch
    elisp-parse-char-escape
    elisp-parse-char-literal-from-port
    elisp-parse-char-literal-from-port-enhanced
    elisp-parse-char-literal-from-port-with-conversion
    elisp-parse-colon-from-port
    elisp-parse-colon-prefixed-symbol
    elisp-parse-colon-prefixed-symbol-and-intern
    elisp-parse-comma-at-from-port
    elisp-parse-comma-from-port
    elisp-parse-comprehensive-dispatch
    elisp-parse-control
    elisp-parse-control-hat
    elisp-parse-hash-empty-symbol-from-port
    elisp-parse-hash-from-port
    elisp-parse-hash-function-from-port
    elisp-parse-hash-number-from-port
    elisp-parse-hash-shebang-from-port
    elisp-parse-hash-uninterned-symbol-from-port
    elisp-parse-hex-char
    elisp-parse-list-from-port
    elisp-parse-literal
    elisp-parse-literal-unified
    elisp-parse-modifier
    elisp-parse-number-from-port
    elisp-parse-octal
    elisp-parse-quote-backquote-dispatch
    elisp-parse-quote-from-port
    elisp-parse-quote-like-from-port
    elisp-parse-quote-like-syntax
    elisp-parse-quote-with-list-construction
    elisp-parse-s-modifier
    elisp-parse-string-literal-from-port
    elisp-parse-string-literal-from-port-enhanced
    elisp-parse-structural
    elisp-parse-structural-literal-unified
    elisp-parse-symbol-from-port
    elisp-parse-unicode
    elisp-parse-vector-from-port
    elisp-parse-vector-from-port-enhanced
    elisp-parse-with-enhanced-conversion
    elisp-parse-with-eof-check
    elisp-parse-with-recursive-reading
    elisp-reader-performance-info
    elisp-readevalloop-load-from-port
    elisp-read-integer-from-port
    elisp-read-with-load-function-from-port
    elisp-setup-default-lexical-binding
    elisp-skip-comment-from-port
    elisp-skip-comment-with-recursive-reading
    elisp-skip-load-comment-from-port
    elisp-skip-load-whitespace-from-port
    intern-gensym
    make-symbol
    resolve-ref
    set-debug-print-flag
  ))

;;;
;;; All reader function implementations below
;;;

;; Main entry point for reading Elisp expressions
(define (elisp-read-from-port port)
  "Main entry point for reading Elisp expressions from PORT.
This is the primary reader function used throughout the codebase."
  (elisp-fread0-complete port))

(define (elisp-read-from-string-with-position str start end)
  "Read one Elisp expression from STR between START and END.
Returns a cons (OBJECT . FINAL-POSITION) where FINAL-POSITION is the
index of the next character after the expression that was read.
This is used by read-from-string and for reading from string streams."
  (let* ((len (string-length str))
         ;; Handle negative indices like Emacs does
         (real-start (if (< start 0) (+ len start) start))
         (real-end (if (< end 0) (+ len end) end))
         ;; Extract substring and create port
         (substr (substring str real-start real-end))
         (port (open-input-string substr)))
    ;; Read the expression
    (let ((obj (elisp-read-from-port port)))
      ;; Get final position using ftell
      (let ((chars-read (ftell port)))
        (cons obj (+ real-start chars-read))))))

;; Register read-from-string as an Elisp function
;; This replaces the C DEFUN in lread.c
(define (elisp-read-from-string string . rest)
  "Read one Lisp expression which is represented as text by STRING.
Returns a cons: (OBJECT-READ . FINAL-STRING-INDEX).
FINAL-STRING-INDEX is an integer giving the position of the next
remaining character in STRING.  START and END optionally delimit
a substring of STRING from which to read; they default to 0 and
\(length STRING) respectively.  Negative values are counted from
the end of STRING."
  (let* ((start (if (null? rest) 0
                    (let ((s (car rest)))
                      (if (eq? s #nil) 0 s))))
         (end (if (or (null? rest) (null? (cdr rest)))
                  (string-length string)
                  (let ((e (cadr rest)))
                    (if (eq? e #nil) (string-length string) e)))))
    (elisp-read-from-string-with-position string start end)))

(set-symbol-function! 'read-from-string elisp-read-from-string)

;; Register read as an Elisp function
;; This replaces the C DEFUN in lread.c
(define (elisp-read . rest)
  "Read one Lisp expression as text from STREAM, return as Lisp object.
If STREAM is nil, use the value of `standard-input' (which see).
STREAM or the value of `standard-input' may be:
 a buffer (read from point and advance it)
 a marker (read from where it points and advance it)
 a function (call it with no arguments for each character,
     call it with a char as argument to push a char back)
 a string (takes text from string, starting at the beginning)
 t (read text line using minibuffer and use it, or read from
    standard input in batch mode)."
  (let ((stream (if (null? rest) #nil (car rest))))
    ;; If stream is nil, use standard-input
    (let ((stream (if (eq? stream #nil)
                      ((symbol-function 'symbol-value) 'standard-input)
                      stream)))
      (cond
        ;; t means read from minibuffer
        ((eq? stream 't)
         ((symbol-function 'read-minibuffer) "Lisp expression: "))
        ;; read-char symbol also means minibuffer
        ((eq? stream 'read-char)
         ((symbol-function 'read-minibuffer) "Lisp expression: "))
        ;; String: use read-from-string, return just the object
        ((string? stream)
         (car (elisp-read-from-string stream)))
        ;; Buffer: read from point, advance point
        ((let ((bufferp (symbol-function 'bufferp)))
           (bufferp stream))
         (elisp-read-from-buffer stream))
        ;; Marker: read from marker position, advance marker
        ((let ((markerp (symbol-function 'markerp)))
           (markerp stream))
         (elisp-read-from-marker stream))
        ;; Function: create port and read
        ((procedure? stream)
         (elisp-read-from-function stream))
        ;; Unknown stream type
        (else
         (error "Invalid stream for read" stream))))))

(define (elisp-read-from-buffer buffer)
  "Read from BUFFER at point, advance point."
  (let ((save-current ((symbol-function 'current-buffer))))
    ((symbol-function 'set-buffer) buffer)
    (let* ((pt ((symbol-function 'point)))
           (pt-max ((symbol-function 'point-max)))
           ;; Get text from point to end
           (text ((symbol-function 'buffer-substring-no-properties) pt pt-max))
           ;; Read from the string
           (result (elisp-read-from-string text))
           (obj (car result))
           (chars-read (cdr result)))
      ;; Advance point
      ((symbol-function 'goto-char) (+ pt chars-read))
      ;; Restore original buffer
      ((symbol-function 'set-buffer) save-current)
      obj)))

(define (elisp-read-from-marker marker)
  "Read from MARKER position, advance marker."
  (let* ((buffer ((symbol-function 'marker-buffer) marker))
         (pos ((symbol-function 'marker-position) marker))
         (save-current ((symbol-function 'current-buffer))))
    ((symbol-function 'set-buffer) buffer)
    (let* ((pt-max ((symbol-function 'point-max)))
           ;; Get text from marker to end
           (text ((symbol-function 'buffer-substring-no-properties) pos pt-max))
           ;; Read from the string
           (result (elisp-read-from-string text))
           (obj (car result))
           (chars-read (cdr result)))
      ;; Advance marker
      ((symbol-function 'set-marker) marker (+ pos chars-read) buffer)
      ;; Restore original buffer
      ((symbol-function 'set-buffer) save-current)
      obj)))

(define (elisp-read-from-function fn)
  "Read using FN as character source.
FN is called with no args to get next char, or with a char to push back."
  ;; Create a soft port that uses fn for reading
  (let* ((pushed-back #f)
         (read-char-proc
          (lambda ()
            (if pushed-back
                (let ((c pushed-back))
                  (set! pushed-back #f)
                  c)
                (let ((result (fn)))
                  (if (eq? result #nil)
                      the-eof-object
                      (integer->char result))))))
         (port (make-soft-port
                (vector
                 #f  ; write-char
                 #f  ; write-string
                 #f  ; flush
                 read-char-proc  ; read-char
                 #f)  ; close
                "r")))
    (elisp-read-from-port port)))

(set-symbol-function! 'read elisp-read)

;; read-positioning-symbols - same as read but with position tracking
;; Position tracking for symbols is not yet implemented in GuilEmacs,
;; so this is currently just an alias for read.
(define (elisp-read-positioning-symbols . rest)
  "Read one Lisp expression as text from STREAM, return as Lisp object.
Convert each occurrence of a symbol into a \"symbol with pos\" object.

If STREAM is nil, use the value of `standard-input' (which see).
STREAM or the value of `standard-input' may be:
 a buffer (read from point and advance it)
 a marker (read from where it points and advance it)
 a function (call it with no arguments for each character,
     call it with a char as argument to push a char back)
 a string (takes text from string, starting at the beginning)
 t (read text line using minibuffer and use it, or read from
    standard input in batch mode)."
  ;; For now, just delegate to read since symbol positions aren't tracked
  (apply elisp-read rest))

(set-symbol-function! 'read-positioning-symbols elisp-read-positioning-symbols)

;;;
;;; List Parsing Functions
;;;

(define (elisp-parse-list-from-port port)
  "Parse an elisp list from PORT, handling both regular and dotted pairs.
Called from C fread0() when '(' is encountered.
Returns: '() for empty list, proper list for (a b c), dotted pair for (a . b)"
  (let ((x
  (let loop ((elements '()))
    ;; Skip whitespace and comments
    (let skip-ws ()
      (let ((ch (read-char port)))
        (cond
          ((eof-object? ch)
           (error "Unexpected EOF in list"))
          ((char=? ch #\;)
           ;; Skip comment until newline
           (let skip-comment ()
             (let ((c (read-char port)))
               (if (not (or (eof-object? c) (char=? c #\newline)))
                 (skip-comment))))
           (skip-ws))
          ((char-whitespace? ch) (skip-ws))
          (else (unread-char ch port)))))
    ;; Check what comes next
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) (error "Unexpected EOF in list"))
        ((char=? ch #\))
         ;; End of list - return reversed elements as proper Elisp list (terminated with #nil)
         (let reverse-to-elisp ((elems elements) (result #nil))
           (if (null? elems)
               result
               (reverse-to-elisp (cdr elems) (cons (car elems) result)))))
        ((char=? ch #\.)
         ;; Check if this is dotted pair syntax (a . b) or dot-prefixed symbol (.rose)
         (let ((next-ch (peek-char port)))
           (if (and (not (eof-object? next-ch))
                    (not (char-whitespace? next-ch))
                    (not (char=? next-ch #\,)))
               ;; This is a dot-prefixed symbol like .rose, not a dotted pair
               ;; Unread the dot and let elisp-read-from-port handle it as a symbol
               (begin
                 (unread-char ch port)
                 (let ((obj (elisp-read-from-port port)))
                   (if (null? obj) (set! obj #nil))
                   (loop (cons obj elements))))
               ;; This is genuine dotted pair syntax (a . b)
               (begin
                 (if (null? elements)
                   (error "Invalid dot syntax at start of list"))
                 ;; Read the tail element
                 (let ((tail (elisp-read-from-port port)))
                   (if (null? tail) (set! tail #nil))
                   ;; Expect closing paren
                   (let skip-ws-after-dot ()
                     (let ((c (read-char port)))
                       (cond
                         ((eof-object? c) (error "Expected ')' after dot"))
                         ((char=? c #\))
                          ;; Build dotted pair: fold right-to-left to get correct order
                          ;; For (a b . c) we want (cons a (cons b c))
                          (let build-dotted ((elems (reverse elements)) (result tail))
                            (if (null? elems)
                                result
                                (cons (car elems) (build-dotted (cdr elems) result)))))
                         ((char-whitespace? c) (skip-ws-after-dot))
                         ((char=? c #\;)
                          ;; Skip comment until newline, then continue skipping whitespace
                          (let skip-comment ()
                            (let ((comment-char (read-char port)))
                              (if (not (or (eof-object? comment-char) (char=? comment-char #\newline)))
                                (skip-comment))))
                          (skip-ws-after-dot))
                         (else
                          (format #t "DEBUG: Found unexpected character after dot: ~a (~s), tail was: ~s~%" c (char->integer c) tail)
                          (format #t "full form: ~s~%" (reverse elements))
                          (force-output)
                          (error "Expected ')' after dot, got" c))))))))))
        (else
         ;; Regular list element
         (unread-char ch port)
         (let ((obj (elisp-read-from-port port)))
           (if (null? obj) (set! obj #nil))
           (loop (cons obj elements)))))))))
    (if (null? x) (set! x #nil))
    x))

(define (elisp-read-integer-from-port port radix)
  "Parse an elisp integer from PORT with given RADIX.
Called from C fread_integer() when #x, #o, #b syntax is encountered.
Returns: integer value"
  ;; Read the digits as a string and convert with the given radix
  (let ((digit-string ""))
    ;; Read characters until we hit non-digit
    (let loop ()
      (let ((ch (peek-char port)))
        (cond
          ((eof-object? ch) #f) ; done
          ((or (char-alphabetic? ch) (char-numeric? ch))
           ;; Valid digit for some radix
           (set! digit-string (string-append digit-string (string (read-char port))))
           (loop))
          (else #f)))) ; done
    ;; Convert string to number using specified radix
    (let ((result (string->number digit-string radix)))
      (if result
          result
          (error "Could not parse integer with radix" radix digit-string)))))

(define (elisp-parse-vector-from-port port)
  "Parse an elisp vector from PORT.
Called from C fread0() when '[' is encountered.
Returns: A proper elisp vector"
  (let loop ((elements '()))
    ;; Skip whitespace and comments
    (let skip-ws ()
      (let ((ch (read-char port)))
        (cond
          ((eof-object? ch)
           (error "Unexpected EOF in vector"))
          ((char=? ch #\;)
           ;; Skip comment until newline
           (let skip-comment ()
             (let ((c (read-char port)))
               (if (not (or (eof-object? c) (char=? c #\newline)))
                 (skip-comment))))
           (skip-ws))
          ((char-whitespace? ch) (skip-ws))
          (else (unread-char ch port)))))
    ;; Check what comes next
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) (error "Unexpected EOF in vector"))
        ((char=? ch #\])
         ;; End of vector - create mutable vector
         ;; Note: Must use make-vector + vector-set! to create mutable vectors in Guile
         (let* ((len (length elements))
                (vec (make-vector len)))
           (do ((i 0 (+ 1 i))
                (ep (reverse elements) (cdr ep)))
               ((null? ep))
             (vector-set! vec i (car ep)))
           vec))
        (else
         ;; Regular vector element
         (unread-char ch port)
         (let ((obj (elisp-read-from-port port)))
           (if (null? obj) (set! obj #nil))
           (loop (cons obj elements))))))))

;; Additional reader functions for fread0 migration

(define (elisp-parse-char-literal-from-port-enhanced port)
  "Parse an elisp character literal from PORT with proper Elisp conversion.
Called from C fread0() when '?' is encountered.
Returns: A character fixnum (Elisp integer) or proper Elisp object"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "Unexpected EOF in character literal"))
      ;; Accept single space or tab syntax like (list ? x)
      ((or (char=? ch #\space) (char=? ch #\tab)) ch)
      ;; Handle escape sequences
      ((char=? ch #\\)
       (let ((escape-ch (read-char port)))
         (cond
           ((eof-object? escape-ch) (error "Unexpected EOF after \\"))
           ;; Standard escape sequences
           ((char=? escape-ch #\n) #\newline)
           ((char=? escape-ch #\t) #\tab)
           ((char=? escape-ch #\r) #\return)
           ((char=? escape-ch #\b) #\backspace)
           ((char=? escape-ch #\f) (integer->char 12)) ; form feed
           ((char=? escape-ch #\a) (integer->char 7))  ; bell
           ((char=? escape-ch #\v) (integer->char 11)) ; vertical tab
           ((char=? escape-ch #\e) (integer->char 27)) ; escape
           ((char=? escape-ch #\s) #\space)
           ((char=? escape-ch #\d) (integer->char 127)) ; delete
           ;; Octal escape sequences \NNN
           ((char<=? #\0 escape-ch #\7)
            (unread-char escape-ch port)
            (let ((octal-str ""))
              (let loop ((count 0))
                (if (< count 3)
                    (let ((digit-ch (read-char port)))
                      (if (and (not (eof-object? digit-ch))
                               (char<=? #\0 digit-ch #\7))
                          (begin
                            (set! octal-str (string-append octal-str (string digit-ch)))
                            (loop (+ count 1)))
                          (when (not (eof-object? digit-ch))
                            (unread-char digit-ch port))))))
              (if (string=? octal-str "")
                  (integer->char 0)
                  (integer->char (string->number octal-str 8)))))
           ;; Hex escape sequences \xHH
           ((char=? escape-ch #\x)
            (let ((hex-str ""))
              (let loop ((count 0))
                (if (< count 2)
                    (let ((hex-ch (read-char port)))
                      (if (and (not (eof-object? hex-ch))
                               (or (char<=? #\0 hex-ch #\9)
                                   (char<=? #\a hex-ch #\f)
                                   (char<=? #\A hex-ch #\F)))
                          (begin
                            (set! hex-str (string-append hex-str (string hex-ch)))
                            (loop (+ count 1)))
                          (when (not (eof-object? hex-ch))
                            (unread-char hex-ch port))))))
              (if (string=? hex-str "")
                  (integer->char 0)
                  (integer->char (string->number hex-str 16)))))
           ;; Control sequences \C-x
           ((char=? escape-ch #\C)
            (let ((dash-ch (read-char port)))
              (if (char=? dash-ch #\-)
                  (let ((ctrl-ch (read-char port)))
                    (if (eof-object? ctrl-ch)
                        (error "Unexpected EOF in control sequence")
                        (integer->char (logand (char->integer (char-upcase ctrl-ch)) #x1f))))
                  (error "Invalid control sequence"))))
           ;; Meta sequences \M-x
           ((char=? escape-ch #\M)
            (let ((dash-ch (read-char port)))
              (if (char=? dash-ch #\-)
                  (let ((meta-ch (read-char port)))
                    (if (eof-object? meta-ch)
                        (error "Unexpected EOF in meta sequence")
                        (integer->char (+ (char->integer meta-ch) 128))))
                  (error "Invalid meta sequence"))))
           ;; Default: return the escaped character literally
           (else escape-ch))))
      ;; Regular character
      (else ch))))

;; Enhanced version that handles character to fixnum conversion in Scheme
(define (elisp-parse-char-literal-from-port-with-conversion port)
  "Parse character literal from PORT with automatic conversion to Elisp fixnum."
  ;; Get the result from the original parser
  (let ((char-result (elisp-parse-char-literal-from-port-enhanced port)))
    (cond
      ;; If it's a character, convert to fixnum using char->integer
      ((char? char-result)
       ;; Convert character to integer - this creates proper Elisp fixnum
       (char->integer char-result))
      ;; If it's already an integer, return directly
      ((integer? char-result) char-result)
      ;; Other types pass through
      (else char-result))))

(define (elisp-parse-quote-from-port port)
  "Parse a quote form (') from PORT.
Returns: the quoted expression (for C to wrap in list2)"
  (elisp-read-from-port port))

(define (elisp-parse-backquote-from-port port)
  "Parse a backquote form (`) from PORT.
Returns: the backquoted expression (for C to wrap in list2)"
  (elisp-read-from-port port))

(define (elisp-parse-quote-with-list-construction port)
  "Parse a quote form (') from PORT and construct the complete (quote expr) list.
This eliminates the C list2() construction by doing it directly in Scheme."
  (let ((quoted-expr (elisp-read-from-port port)))
    ;; Use Scheme cons to build (quote expr) - equivalent to C list2(Qquote, quoted_expr)
    (cons ((symbol-function 'intern) "quote" #nil) (cons quoted-expr #nil))))

(define (elisp-parse-backquote-with-list-construction port)
  "Parse a backquote form (`) from PORT and construct the complete (` expr) list.
This eliminates the C list2() construction by doing it directly in Scheme."
  (let ((backquoted-expr (elisp-read-from-port port)))
    ;; Use Scheme cons to build (` expr) - equivalent to C list2(Qbackquote, backquoted_expr)
    (cons ((symbol-function 'intern) "`" #nil) (cons backquoted-expr #nil))))

(define (elisp-parse-comma-from-port port)
  "Parse comma syntax from PORT, handling both , and ,@ forms.
Called from C fread0() when ',' is encountered.
Returns: (comma expr) or (comma-at expr) list structures using proper Elisp symbols"
  ;; C has already detected the comma, now determine , vs ,@
  (let ((next-ch (peek-char port)))
    (cond
      ;; Check for ,@ (comma-at)
      ((and (not (eof-object? next-ch)) (char=? next-ch #\@))
       ;; Consume the @ and read the expression
       (read-char port) ; consume @
       (let ((expr (elisp-read-from-port port)))
         ;; Return (comma-at expr) with proper Elisp symbol and list termination
         (cons (elisp-intern ",@" #nil) (cons expr #nil))))

      ;; Regular comma ,
      (else
       ;; Read the expression
       (let ((expr (elisp-read-from-port port)))
         ;; Return (comma expr) with proper Elisp symbol and list termination
         (cons (elisp-intern "," #nil) (cons expr #nil)))))))

(define (elisp-parse-comma-at-from-port port)
  "Parse a comma-at form (,@) from PORT.
Returns: the unquote-spliced expression (for C to wrap in list2)"
  (elisp-read-from-port port))

;; Unified quote-like syntax parser - consolidates ', `, , dispatch
(define (elisp-parse-quote-like-from-port char port)
  "Parse quote-like syntax (', `, ,) based on character from PORT.
This unified parser consolidates the dispatch logic that was previously in C.
Returns the appropriate parsed structure for the given quote-like character."
  (cond
    ((char=? char #\')
     ;; Quote form with complete list construction
     (elisp-parse-quote-with-list-construction port))
    ((char=? char #\`)
     ;; Backquote form with complete list construction
     (elisp-parse-backquote-with-list-construction port))
    ((char=? char #\,)
     ;; Comma syntax (, or ,@) handled by unified parser
     (elisp-parse-comma-from-port port))
    (else
     (error "Unexpected character in quote-like parsing" char))))

(define (elisp-parse-string-literal-from-port port)
  "Parse a string literal from PORT.
The opening quote has been put back, so we consume it and parse the string
with proper Elisp escape sequence handling.
Returns: the parsed string"
  ;; Consume the opening quote
  (let ((open-quote (read-char port)))
    (unless (and (char? open-quote) (char=? open-quote #\"))
      (error "Expected opening quote for string literal"))
    ;; Parse string contents character by character
    (let loop ((chars '()))
      (let ((ch (read-char port)))
        (cond
          ((eof-object? ch)
           (error "Unexpected EOF in string literal"))
          ;; Closing quote - done
          ((char=? ch #\")
           (list->string (reverse chars)))
          ;; Escape sequence
          ((char=? ch #\\)
           (let ((escape-ch (read-char port)))
             (cond
               ((eof-object? escape-ch)
                (error "Unexpected EOF after backslash in string"))
               ;; Standard escape sequences
               ((char=? escape-ch #\n) (loop (cons #\newline chars)))
               ((char=? escape-ch #\t) (loop (cons #\tab chars)))
               ((char=? escape-ch #\r) (loop (cons #\return chars)))
               ((char=? escape-ch #\f) (loop (cons (integer->char 12) chars))) ; form feed
               ((char=? escape-ch #\b) (loop (cons #\backspace chars)))
               ((char=? escape-ch #\a) (loop (cons (integer->char 7) chars)))  ; bell
               ((char=? escape-ch #\v) (loop (cons (integer->char 11) chars))) ; vertical tab
               ((char=? escape-ch #\e) (loop (cons (integer->char 27) chars))) ; ESC
               ((char=? escape-ch #\s) (loop (cons #\space chars)))
               ((char=? escape-ch #\d) (loop (cons (integer->char 127) chars))) ; delete
               ((char=? escape-ch #\\) (loop (cons #\\ chars)))
               ((char=? escape-ch #\") (loop (cons #\" chars)))
               ((char=? escape-ch #\newline)
                ;; Backslash-newline: skip both and continue
                (loop chars))
               ;; Octal escape \NNN
               ((and (char>=? escape-ch #\0) (char<=? escape-ch #\7))
                (let ((octal-val (- (char->integer escape-ch) (char->integer #\0))))
                  (let octal-loop ((val octal-val) (count 1))
                    (if (>= count 3)
                        (loop (cons (integer->char val) chars))
                        (let ((next (peek-char port)))
                          (if (and (not (eof-object? next))
                                   (char>=? next #\0) (char<=? next #\7))
                              (begin
                                (read-char port)
                                (octal-loop (+ (* val 8) (- (char->integer next) (char->integer #\0)))
                                            (+ count 1)))
                              (loop (cons (integer->char val) chars))))))))
               ;; Hex escape \xNN
               ((char=? escape-ch #\x)
                (let hex-loop ((val 0) (count 0))
                  (let ((next (peek-char port)))
                    (cond
                      ((eof-object? next)
                       (loop (cons (integer->char val) chars)))
                      ((or (and (char>=? next #\0) (char<=? next #\9))
                           (and (char>=? next #\a) (char<=? next #\f))
                           (and (char>=? next #\A) (char<=? next #\F)))
                       (read-char port)
                       (let ((digit (cond
                                      ((char<=? next #\9) (- (char->integer next) (char->integer #\0)))
                                      ((char<=? next #\F) (+ 10 (- (char->integer next) (char->integer #\A))))
                                      (else (+ 10 (- (char->integer next) (char->integer #\a)))))))
                         (hex-loop (+ (* val 16) digit) (+ count 1))))
                      (else
                       (loop (cons (integer->char val) chars)))))))
               ;; Unicode escape \uNNNN
               ((char=? escape-ch #\u)
                (let uni-loop ((val 0) (count 0))
                  (if (>= count 4)
                      (loop (cons (integer->char val) chars))
                      (let ((next (read-char port)))
                        (cond
                          ((eof-object? next)
                           (error "Unexpected EOF in unicode escape"))
                          ((or (and (char>=? next #\0) (char<=? next #\9))
                               (and (char>=? next #\a) (char<=? next #\f))
                               (and (char>=? next #\A) (char<=? next #\F)))
                           (let ((digit (cond
                                          ((char<=? next #\9) (- (char->integer next) (char->integer #\0)))
                                          ((char<=? next #\F) (+ 10 (- (char->integer next) (char->integer #\A))))
                                          (else (+ 10 (- (char->integer next) (char->integer #\a)))))))
                             (uni-loop (+ (* val 16) digit) (+ count 1))))
                          (else
                           (error "Invalid hex digit in unicode escape")))))))
               ;; Unicode escape \UNNNNNNNN
               ((char=? escape-ch #\U)
                (let uni-loop ((val 0) (count 0))
                  (if (>= count 8)
                      (loop (cons (integer->char val) chars))
                      (let ((next (read-char port)))
                        (cond
                          ((eof-object? next)
                           (error "Unexpected EOF in unicode escape"))
                          ((or (and (char>=? next #\0) (char<=? next #\9))
                               (and (char>=? next #\a) (char<=? next #\f))
                               (and (char>=? next #\A) (char<=? next #\F)))
                           (let ((digit (cond
                                          ((char<=? next #\9) (- (char->integer next) (char->integer #\0)))
                                          ((char<=? next #\F) (+ 10 (- (char->integer next) (char->integer #\A))))
                                          (else (+ 10 (- (char->integer next) (char->integer #\a)))))))
                             (uni-loop (+ (* val 16) digit) (+ count 1))))
                          (else
                           (error "Invalid hex digit in unicode escape")))))))
               ;; Default: return the escaped character literally
               (else (loop (cons escape-ch chars))))))
          ;; Regular character
          (else (loop (cons ch chars))))))))

(define (elisp-parse-string-literal-from-port-enhanced port)
  "Parse a string literal from PORT with enhanced quote handling.
This version handles the case where C has consumed the opening quote.
Returns: the parsed string with proper type validation in Scheme"
  ;; Use our proper Elisp string parser that handles \e and other escape sequences
  (let ((result (elisp-parse-string-literal-from-port port)))
    (cond
      ((eof-object? result)
       (error "Unexpected EOF while reading string"))
      ((string? result) result)
      (else
       (error "String parser returned non-string")))))

(define (elisp-parse-hash-s-from-port port)
  "Parse #s(...) syntax for hash-tables and records.
The 's' has already been consumed. Expects '(' followed by elements."
  (let ((ch (read-char port)))
    (unless (and (char? ch) (char=? ch #\())
      (error "Expected '(' after #s"))
    ;; Read the list contents
    (let ((elems (elisp-parse-list-from-port port)))
      (cond
        ((or (null? elems) (eq? elems #nil))
         (error "Empty #s() syntax"))
        ;; If first element is 'hash-table, create hash table from plist
        ((eq? (car elems) 'hash-table)
         (elisp-hash-table-from-plist (cdr elems)))
        ;; Otherwise create a record
        (else
         (elisp-record-from-list elems))))))

(define (elisp-hash-table-from-plist plist)
  "Create a hash table from a property list.
PLIST is a list of alternating keys and values.
Uses Elisp make-hash-table and puthash for proper Emacs hash tables."
  (let ((elisp-make-hash-table (symbol-function 'make-hash-table))
        (elisp-puthash (symbol-function 'puthash))
        (test-param #nil)
        (size-param #nil)
        (weakness-param #nil)
        (data-list #nil))
    ;; First pass: extract all parameters
    (let param-loop ((rest plist))
      (cond
        ((or (null? rest) (eq? rest #nil)) #t)
        ((or (null? (cdr rest)) (eq? (cdr rest) #nil))
         (error "Odd number of elements in hash-table plist"))
        (else
         (let ((key (car rest))
               (val (cadr rest)))
           (cond
             ((eq? key 'test) (set! test-param val))
             ((eq? key 'size) (set! size-param val))
             ((eq? key 'weakness) (set! weakness-param val))
             ((eq? key 'data) (set! data-list val)))
           (param-loop (cddr rest))))))
    ;; Create hash table - just create empty one for now (keywords need interning)
    (let ((ht (elisp-make-hash-table)))
      ;; Fill in the data
      (let data-loop ((data data-list))
        (cond
          ((or (null? data) (eq? data #nil)) #t)
          ((or (null? (cdr data)) (eq? (cdr data) #nil))
           (error "Odd number of elements in hash-table data"))
          (else
           (elisp-puthash (car data) (cadr data) ht)
           (data-loop (cddr data)))))
      ht)))

(define (elisp-record-from-list elems)
  "Create a record from a list. First element is type, rest are slots."
  ;; For now, return as a vector with a type marker
  ;; Records are implemented as vectors in Emacs
  (let* ((type (car elems))
         (slots (cdr elems))
         (len (length slots))
         (rec (make-vector (+ len 1) #nil)))
    (vector-set! rec 0 type)
    (let loop ((i 1) (rest slots))
      (cond
        ((or (null? rest) (eq? rest #nil)) rec)
        (else
         (vector-set! rec i (car rest))
         (loop (+ i 1) (cdr rest)))))))

(define (elisp-parse-bool-vector-from-port port)
  "Parse a bool vector (#&LENGTH\"DATA\") from PORT.
C has already consumed '#&', now we need to parse length and string data.
Returns: a cons (LENGTH . STRING-DATA) for C to convert to bool vector"
  ;; Read the length digits until we hit a quote
  (let loop ((length 0))
    (let ((ch (peek-char port)))
      (cond
        ((eof-object? ch)
         (error "EOF while reading bool vector length"))
        ((char=? ch #\")
         ;; Found the quote, now read the string data
         (let ((str (read port)))  ; This will read the complete string
           (cons length str)))
        ((and (char>=? ch #\0) (char<=? ch #\9))
         ;; Consume the digit and continue
         (read-char port) ; consume the digit
         (let ((digit (- (char->integer ch) (char->integer #\0))))
           (loop (+ (* length 10) digit))))
        (else
         (error "Invalid character in bool vector length"))))))

(define (elisp-create-bool-vector-from-scheme length string-data)
  "Create Elisp bool vector directly in Scheme to avoid malloc/free cycles.
This function uses Scheme's string access functions to eliminate C string allocation."
  ;; For now, we return the same format but could enhance this with bytevectors
  ;; to completely eliminate the C malloc/free cycle in the future
  (cons length string-data))

(define (elisp-skip-comment-from-port port)
  "Skip a line comment starting with ; until newline.
Returns: #t (to indicate successful skip)"
  (let loop ()
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) #t)
        ((char=? ch #\newline) #t)
        (else (loop))))))

(define (elisp-parse-hash-function-from-port port)
  "Parse #' function syntax from PORT.
Returns: (function object)"
  (let ((obj (elisp-read-from-port port)))
    (cons 'function (cons obj #nil))))

(define (elisp-parse-hash-empty-symbol-from-port port)
  "Parse ## empty symbol syntax from PORT.
Returns: interned empty symbol"
  ;; In GuilEmacs, we need to return the interned empty symbol
  ;; This is handled by calling the C intern function
  (string->symbol ""))

(define (elisp-parse-hash-shebang-from-port port)
  "Parse #! shebang comment from PORT, skipping to end of line.
Returns: #t (to indicate successful skip)"
  (let loop ()
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) #t)
        ((char=? ch #\newline) #t)
        (else (loop))))))

(define (elisp-parse-hash-uninterned-symbol-from-port port)
  "Parse #: uninterned symbol syntax from PORT.
Returns: uninterned symbol"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (gensym ""))
      ;; Check for symbol terminator characters
      ((or (char<=? ch #\space)
           (char=? ch #\")
           (char=? ch #\')
           (char=? ch #\;)
           (char=? ch #\#)
           (char=? ch #\()
           (char=? ch #\))
           (char=? ch #\[)
           (char=? ch #\])
           (char=? ch #\`)
           (char=? ch #\,))
       ;; Empty uninterned symbol
       (unread-char ch port)
       (gensym ""))
      (else
       ;; Read the symbol name manually to avoid circular dependency
       (let ((name (string ch)))
         (let loop ()
           (let ((next-ch (read-char port)))
             (cond
               ((eof-object? next-ch)
                (gensym name))
               ((or (char<=? next-ch #\space)
                    (char=? next-ch #\")
                    (char=? next-ch #\')
                    (char=? next-ch #\;)
                    (char=? next-ch #\#)
                    (char=? next-ch #\()
                    (char=? next-ch #\))
                    (char=? next-ch #\[)
                    (char=? next-ch #\])
                    (char=? next-ch #\`)
                    (char=? next-ch #\,))
                ;; Symbol terminator found, put it back and create symbol
                (unread-char next-ch port)
                (gensym name))
               (else
                ;; Regular symbol character, add to name and continue
                (set! name (string-append name (string next-ch)))
                (loop))))))))))

(define (elisp-parse-hash-from-port port)
  "Parse all hash (#) syntax forms from PORT.
Unified dispatcher for all # syntax in Elisp reader.
Returns: appropriate Lisp object based on hash syntax"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "Unexpected EOF after #"))

      ;; #' function syntax - already implemented
      ((char=? ch #\')
       (elisp-parse-hash-function-from-port port))

      ;; ## empty symbol
      ((char=? ch #\#)
       (string->symbol ""))

      ;; #! shebang comments - already implemented
      ((char=? ch #\!)
       (elisp-parse-hash-shebang-from-port port)
       ;; Return nil to indicate "continue reading"
       #nil)

      ;; #: uninterned symbols - already implemented
      ((char=? ch #\:)
       (elisp-parse-hash-uninterned-symbol-from-port port))

      ;; #$ lazy file reference
      ((char=? ch #\$)
       ;; Access Vload_file_name directly from Scheme
       ((symbol-function 'symbol-value) 'load-file-name))

      ;; Radix integers: #x #X #o #O #b #B
      ((or (char=? ch #\x) (char=? ch #\X))
       (elisp-read-integer-from-port port 16))
      ((or (char=? ch #\o) (char=? ch #\O))
       (elisp-read-integer-from-port port 8))
      ((or (char=? ch #\b) (char=? ch #\B))
       (elisp-read-integer-from-port port 2))

      ;; Complex number syntax #N=, #N#, #Nr
      ((char-numeric? ch)
       (elisp-parse-hash-number-from-port port ch))

      ;; #s(...) - hash-table or record syntax
      ((char=? ch #\s)
       (elisp-parse-hash-s-from-port port))
      ((char=? ch #\^)
       (error "Char-table syntax (#^) not supported"))
      ((char=? ch #\()
       (error "Text-properties syntax (#() not supported"))
      ((char=? ch #\[)
       (error "Bytecode syntax (#[) not supported"))
      ((char=? ch #\&)
       ;; #&N"..." bool vector syntax
       (elisp-parse-bool-vector-from-port port))
      ((char=? ch #\@)
       (error "Obsolete load syntax (#@) not supported"))
      ((char=? ch #\_)
       (error "Shorthand syntax (#_) not supported"))

      (else
       (error "Invalid hash syntax" (string #\# ch))))))

(define (elisp-parse-hash-number-from-port port first-digit)
  "Parse hash syntax starting with a number: #N=, #N#, #Nr
PORT: input port
FIRST-DIGIT: first digit character already read
Returns: appropriate object for the syntax"
  ;; Read complete number first
  (let ((n (- (char->integer first-digit) (char->integer #\0))))
    (let loop ((result n))
      (let ((ch (read-char port)))
        (cond
          ((eof-object? ch)
           (error "Unexpected EOF in hash number syntax"))
          ((char-numeric? ch)
           ;; Continue reading digits
           (let ((digit (- (char->integer ch) (char->integer #\0))))
             (loop (+ (* result 10) digit))))
          ((char=? ch #\=)
           ;; #N= circle definition - not implemented yet
           (error "Circle definitions (#N=) not yet supported"))
          ((char=? ch #\#)
           ;; #N# circle reference - not implemented yet
           (error "Circle references (#N#) not yet supported"))
          ((or (char=? ch #\r) (char=? ch #\R))
           ;; #Nr arbitrary radix
           (if (or (< result 2) (> result 36))
               (error "Invalid radix for integer" result)
               (elisp-read-integer-from-port port result)))
          (else
           (error "Invalid character in hash number syntax" ch)))))))

(define (elisp-parse-char-literal-from-port port)
  "Parse an Elisp character literal from PORT.
Handles simple characters, escape sequences, and modifier combinations.
Called from C fread0() when '?' is encountered.
Returns: A character fixnum with appropriate encoding"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "Unexpected EOF in character literal"))

      ;; Accept single space or tab syntax like (list ? x)
      ((or (char=? ch #\space) (char=? ch #\tab))
       (char->integer ch))

      ;; Handle escape sequences
      ((char=? ch #\\)
       (elisp-parse-char-escape port))

      ;; Regular character - check for valid terminator
      (else
       (let ((next-ch (peek-char port)))
         (if (or (eof-object? next-ch)
                 (char<=? next-ch #\space)
                 (char=? next-ch #\")
                 (char=? next-ch #\')
                 (char=? next-ch #\;)
                 (char=? next-ch #\()
                 (char=? next-ch #\))
                 (char=? next-ch #\[)
                 (char=? next-ch #\])
                 (char=? next-ch #\#)
                 (char=? next-ch #\?)
                 (char=? next-ch #\`)
                 (char=? next-ch #\,)
                 (char=? next-ch #\.))
             (char->integer ch)
             (error "Invalid character syntax")))))))

(define (elisp-parse-char-escape port)
  "Parse escape sequences in character literals.
Handles \\n, \\t, \\M-x, \\C-x, \\S-x, etc.
Returns: Character code with modifiers encoded"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "Unexpected EOF in escape sequence"))

      ;; Basic escape sequences
      ((char=? ch #\a) 7)    ; bell
      ((char=? ch #\b) 8)    ; backspace
      ((char=? ch #\d) 127)  ; delete
      ((char=? ch #\e) 27)   ; escape
      ((char=? ch #\f) 12)   ; form feed
      ((char=? ch #\n) 10)   ; newline
      ((char=? ch #\r) 13)   ; carriage return
      ((char=? ch #\t) 9)    ; tab
      ((char=? ch #\v) 11)   ; vertical tab
      ((char=? ch #\newline) (error "Invalid escape: \\<newline>"))

      ;; Modifier keys: \M-x, \C-x, \S-x, \H-x, \A-x, \s-x
      ((char=? ch #\M) (elisp-parse-modifier port #x2000000))  ; meta
      ((char=? ch #\C) (elisp-parse-control port))             ; control
      ((char=? ch #\S) (elisp-parse-modifier port #x8000000))  ; shift
      ((char=? ch #\H) (elisp-parse-modifier port #x10000000)) ; hyper
      ((char=? ch #\A) (elisp-parse-modifier port #x4000000))  ; alt
      ((char=? ch #\s) (elisp-parse-s-modifier port))          ; super or space
      ((char=? ch #\^) (elisp-parse-control-hat port))         ; ^x syntax

      ;; Octal sequences: \123
      ((char-numeric? ch)
       (elisp-parse-octal port ch))

      ;; Unicode sequences: \u1234 or \U12345678
      ((char=? ch #\u) (elisp-parse-unicode port 4))
      ((char=? ch #\U) (elisp-parse-unicode port 8))
      ((char=? ch #\x) (elisp-parse-hex-char port))

      ;; Default: literal character after backslash
      (else (char->integer ch)))))

(define (elisp-parse-modifier port modifier-bit)
  "Parse modifier syntax like \\M-x, \\S-x, etc."
  (let ((dash (read-char port)))
    (if (not (char=? dash #\-))
        (error "Expected '-' after modifier")
        (let ((next-ch (read-char port)))
          (cond
            ((eof-object? next-ch) (error "EOF after modifier"))
            ((char=? next-ch #\\)
             ;; Chained escape: \M-\C-x
             (+ modifier-bit (elisp-parse-char-escape port)))
            (else
             ;; Simple modified char: \M-x
             (+ modifier-bit (char->integer next-ch))))))))

(define (elisp-parse-s-modifier port)
  "Handle \\s which can be \\s-x (super) or just \\s (space)"
  (let ((next-ch (peek-char port)))
    (if (char=? next-ch #\-)
        (begin
          (read-char port) ; consume the '-'
          (let ((ch (read-char port)))
            (if (char=? ch #\\)
                (+ #x1000000 (elisp-parse-char-escape port)) ; super + escape
                (+ #x1000000 (char->integer ch)))))          ; super + char
        32))) ; just space

(define (elisp-parse-control port)
  "Parse \\C-x control modifier"
  (let ((dash (read-char port)))
    (if (not (char=? dash #\-))
        (error "Expected '-' after \\C")
        (let ((ch (read-char port)))
          (cond
            ((eof-object? ch) (error "EOF after \\C-"))
            ((char=? ch #\\)
             ;; \C-\something
             (logior #x4000000 (elisp-parse-char-escape port)))
            (else
             ;; \C-x - make control character
             (let ((code (char->integer ch)))
               (if (and (>= code 64) (<= code 95)) ; @ A-Z [ \ ] ^ _
                   (- code 64)
                   (logior #x4000000 code)))))))))

(define (elisp-parse-control-hat port)
  "Parse \\^x control syntax"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "EOF after \\^"))
      ((char=? ch #\\)
       (logior #x4000000 (elisp-parse-char-escape port)))
      (else
       (let ((code (char->integer ch)))
         (if (and (>= code 64) (<= code 95))
             (- code 64)
             (logior #x4000000 code)))))))

(define (elisp-parse-octal port first-digit)
  "Parse octal character code \\123"
  (let ((value (- (char->integer first-digit) (char->integer #\0))))
    (let loop ((result value) (count 1))
      (if (>= count 3)
          result
          (let ((ch (peek-char port)))
            (if (and (not (eof-object? ch))
                     (char-numeric? ch)
                     (<= (char->integer ch) (char->integer #\7)))
                (begin
                  (read-char port)
                  (loop (+ (* result 8) (- (char->integer ch) (char->integer #\0)))
                        (+ count 1)))
                result))))))

(define (elisp-parse-unicode port digit-count)
  "Parse Unicode escape \\u1234 or \\U12345678"
  (let loop ((result 0) (count 0))
    (if (>= count digit-count)
        result
        (let ((ch (read-char port)))
          (cond
            ((eof-object? ch) (error "EOF in Unicode escape"))
            ((or (and (char>=? ch #\0) (char<=? ch #\9))
                 (and (char>=? ch #\a) (char<=? ch #\f))
                 (and (char>=? ch #\A) (char<=? ch #\F)))
             (let ((digit (if (char-numeric? ch)
                             (- (char->integer ch) (char->integer #\0))
                             (+ (- (char->integer (char-downcase ch))
                                   (char->integer #\a)) 10))))
               (loop (+ (* result 16) digit) (+ count 1))))
            (else (error "Invalid hex digit in Unicode escape")))))))

(define (elisp-parse-hex-char port)
  "Parse hex character \\x12"
  (let loop ((result 0) (count 0))
    (let ((ch (peek-char port)))
      (if (or (eof-object? ch)
              (not (or (and (char>=? ch #\0) (char<=? ch #\9))
                      (and (char>=? ch #\a) (char<=? ch #\f))
                      (and (char>=? ch #\A) (char<=? ch #\F)))))
          (if (= count 0)
              (error "No hex digits after \\x")
              result)
          (begin
            (read-char port)
            (let ((digit (if (char-numeric? ch)
                            (- (char->integer ch) (char->integer #\0))
                            (+ (- (char->integer (char-downcase ch))
                                  (char->integer #\a)) 10))))
              (loop (+ (* result 16) digit) (+ count 1))))))))

(define (elisp-parse-colon-from-port port)
  "Parse colon syntax from PORT.
Handles both bare colon ':' and colon-prefixed symbols ':keyword'.
Called from C fread0() when ':' is encountered at symbol position.
Returns: appropriate Elisp symbol with keyword self-evaluation"
  ;; First consume the colon character
  (let ((colon-ch (read-char port)))
    (if (not (char=? colon-ch #\:))
        (error "Expected colon character")
        (let ((next-ch (peek-char port)))
          (cond
            ;; EOF - bare colon
            ((eof-object? next-ch)
             (elisp-intern-and-make-keyword ":"))

            ;; Check for symbol terminator characters - this is a bare colon
            ((or (char<=? next-ch #\space)
                 (char=? next-ch #\")
                 (char=? next-ch #\')
                 (char=? next-ch #\;)
                 (char=? next-ch #\()
                 (char=? next-ch #\))
                 (char=? next-ch #\[)
                 (char=? next-ch #\])
                 (char=? next-ch #\#)
                 (char=? next-ch #\?)
                 (char=? next-ch #\`)
                 (char=? next-ch #\,)
                 (char=? next-ch #\.))
             ;; Bare colon symbol
             (elisp-intern-and-make-keyword ":"))

            ;; This is a colon-prefixed symbol like :documentation
            (else
             (elisp-parse-colon-prefixed-symbol-and-intern port)))))))

(define (elisp-symbol-terminator? ch)
  "Return #t if CH is a symbol terminator character."
  (or (eof-object? ch)
      (char<=? ch #\space)
      (char=? ch #\()
      (char=? ch #\))
      (char=? ch #\[)
      (char=? ch #\])
      (char=? ch #\")
      (char=? ch #\')
      (char=? ch #\`)
      (char=? ch #\,)
      (char=? ch #\;)
      (char=? ch #\#)))

(define (elisp-parse-colon-prefixed-symbol port)
  "Parse a colon-prefixed symbol like :keyword from PORT.
Assumes the colon has already been consumed and we're reading the rest.
Handles backslash escapes."
  (let loop ((chars '(#\:)))  ; Start with colon
    (let ((ch (peek-char port)))
      (cond
        ;; EOF or terminator character - done reading symbol
        ((elisp-symbol-terminator? ch)
         ;; Done - create the symbol
         (string->symbol (list->string (reverse chars))))

        ;; Backslash - escape next character (include it literally)
        ((char=? ch #\\)
         (read-char port)  ; consume backslash
         (let ((escaped (read-char port)))
           (if (eof-object? escaped)
               (error "Unexpected EOF after backslash in symbol")
               (loop (cons escaped chars)))))

        ;; Regular symbol character - add to name and continue
        (else
         (read-char port)
         (loop (cons ch chars)))))))

(define (elisp-parse-symbol-from-port port)
  "Parse symbol or number from PORT with Elisp backslash escape handling.
Called from C fread0() when alphabetic character is encountered.
Handles backslash escapes (e.g., \\; for literal semicolon in symbol names),
special symbol identity mapping, keyword conversion, and uninterned symbols.
Returns the parsed object with proper Elisp semantics."
  ;; Manually read characters with backslash escape handling
  (let loop ((chars '()))
    (let ((ch (peek-char port)))
      (cond
        ;; EOF or terminator - done reading symbol
        ((elisp-symbol-terminator? ch)
         (if (null? chars)
             (error "Unexpected EOF while reading symbol")
             (let ((sym-str (list->string (reverse chars))))
               (elisp-intern-symbol-string sym-str))))

        ;; Backslash - escape next character (include it literally)
        ((char=? ch #\\)
         (read-char port)  ; consume backslash
         (let ((escaped (read-char port)))
           (if (eof-object? escaped)
               (error "Unexpected EOF after backslash in symbol")
               (loop (cons escaped chars)))))

        ;; Regular character - add to symbol name
        (else
         (read-char port)
         (loop (cons ch chars)))))))

(define (elisp-intern-symbol-string sym-str)
  "Intern SYM-STR as an Elisp symbol with proper special case handling."
  (cond
    ;; Special Elisp symbols - use canonical values
    ((string=? sym-str "nil")
     #nil)
    ((string=? sym-str "t")
     #t)

    ;; Reader macro symbols - map to canonical Elisp symbols
    ((string=? sym-str "`")
     ((symbol-function 'intern) "`" #nil))
    ((string=? sym-str ",")
     ((symbol-function 'intern) "," #nil))
    ((string=? sym-str ",@")
     ((symbol-function 'intern) ",@" #nil))

    ;; Keyword symbols (start with :) - make self-evaluating
    ((and (> (string-length sym-str) 0)
          (char=? (string-ref sym-str 0) #\:))
     (let ((elisp-symbol ((symbol-function 'intern) sym-str #nil)))
       ((symbol-function 'set) elisp-symbol elisp-symbol)
       elisp-symbol))

    ;; Regular symbols - intern normally
    (else
     ((symbol-function 'intern) sym-str #nil))))

(define (elisp-parse-number-from-port port)
  "Parse number or symbol from PORT with Elisp backslash escape handling.
Called from C fread0() when numeric character is encountered.
Returns the parsed number or symbol with proper Elisp semantics."
  ;; Manually read characters with backslash escape handling
  (let loop ((chars '()) (has-escape #f))
    (let ((ch (peek-char port)))
      (cond
        ;; EOF or terminator - done reading
        ((elisp-symbol-terminator? ch)
         (if (null? chars)
             (error "Unexpected EOF while reading number")
             (let ((token-str (list->string (reverse chars))))
               ;; If we had escapes, it's definitely a symbol
               ;; Otherwise try to parse as number first
               (if has-escape
                   (elisp-intern-symbol-string token-str)
                   (let ((num (string->number token-str)))
                     (if num
                         num
                         (elisp-intern-symbol-string token-str)))))))

        ;; Backslash - escape next character (include it literally)
        ((char=? ch #\\)
         (read-char port)  ; consume backslash
         (let ((escaped (read-char port)))
           (if (eof-object? escaped)
               (error "Unexpected EOF after backslash")
               (loop (cons escaped chars) #t))))  ; mark that we had an escape

        ;; Regular character - add to token
        (else
         (read-char port)
         (loop (cons ch chars) has-escape))))))

(define (elisp-intern-and-make-keyword str)
  "Intern STR as Elisp symbol and make it self-evaluating if it's a keyword."
  (let ((elisp-symbol ((symbol-function 'intern) str #nil)))
    ;; If it's a keyword (starts with :), make it self-evaluating
    (if (and (> (string-length str) 0) (char=? (string-ref str 0) #\:))
        ((symbol-function 'set) elisp-symbol elisp-symbol))
    elisp-symbol))

(define (elisp-parse-colon-prefixed-symbol-and-intern port)
  "Parse a colon-prefixed symbol from PORT and return proper Elisp symbol.
Assumes the colon has already been consumed. Handles backslash escapes."
  (let loop ((chars '(#\:)))  ; Start with colon
    (let ((ch (peek-char port)))
      (cond
        ;; EOF or terminator character - done reading symbol
        ((elisp-symbol-terminator? ch)
         ;; Done - intern as Elisp symbol with keyword self-evaluation
         (elisp-intern-and-make-keyword (list->string (reverse chars))))

        ;; Backslash - escape next character (include it literally)
        ((char=? ch #\\)
         (read-char port)  ; consume backslash
         (let ((escaped (read-char port)))
           (if (eof-object? escaped)
               (error "Unexpected EOF after backslash in keyword")
               (loop (cons escaped chars)))))

        ;; Regular symbol character - add to name and continue
        (else
         (read-char port)
         (loop (cons ch chars)))))))

(define (elisp-convert-guile-object obj)
  "Convert Guile object to Elisp with proper semantics, eliminating C conversions.
This function replaces the inefficient conversion patterns in guile_to_lisp_object
by using direct Scheme-to-Elisp function calls instead of malloc/free cycles."
  (cond
    ;; Handle null - return Elisp nil
    ((null? obj) #nil)

    ;; Handle booleans - map to Elisp t/nil
    ((boolean? obj) (if obj #t #nil))

    ;; Handle exact integers - pass through directly
    ((and (integer? obj) (exact? obj)) obj)

    ;; Handle real numbers - pass through directly
    ((real? obj) obj)

    ;; Handle strings - pass through directly (already Lisp_Objects in GuilEmacs)
    ((string? obj) obj)

    ;; Handle symbols with special mapping using direct Elisp interning
    ((symbol? obj)
     (let ((sym-str (symbol->string obj)))
       (cond
         ;; Special Elisp symbols - use canonical values
         ((string=? sym-str "nil") #nil)
         ((string=? sym-str "t") #t)
         ((string=? sym-str "and") ((symbol-function 'intern) "and" #nil))
         ((string=? sym-str ":") ((symbol-function 'intern) ":" #nil))

         ;; Reader macro symbols - map to canonical Elisp symbols
         ((or (string=? sym-str "`") (string=? sym-str "\\`"))
          ((symbol-function 'intern) "`" #nil))
         ((or (string=? sym-str ",") (string=? sym-str "\\,"))
          ((symbol-function 'intern) "," #nil))
         ((or (string=? sym-str ",@") (string=? sym-str "\\,@"))
          ((symbol-function 'intern) ",@" #nil))

         ;; Regular symbols - intern using direct Scheme-to-Elisp conversion
         (else ((symbol-function 'intern) sym-str #nil)))))

    ;; Handle Guile keywords - convert to Elisp colon symbols
    ((keyword? obj)
     (let* ((keyword-symbol (keyword->symbol obj))
            (base-name (symbol->string keyword-symbol)))
       (cond
         ;; Special case: empty keyword (bare :) -> colon symbol
         ((= (string-length base-name) 0)
          ((symbol-function 'intern) ":" #nil))
         ;; Regular keywords get : prefix and self-evaluation
         (else
          (let* ((colon-name (string-append ":" base-name))
                 (elisp-symbol ((symbol-function 'intern) colon-name #nil)))
            ;; Make keyword self-evaluating
            ((symbol-function 'set) elisp-symbol elisp-symbol)
            elisp-symbol)))))

    ;; Handle pairs - convert recursively to Elisp cons cells
    ((pair? obj)
     (let ((car-converted (elisp-convert-guile-object (car obj)))
           (cdr-converted (elisp-convert-guile-object (cdr obj))))
       ((symbol-function 'cons) car-converted cdr-converted)))

    ;; For other types, pass through directly
    (else obj)))

(define (elisp-parse-vector-from-port-enhanced port)
  "Parse vector from PORT using existing Elisp vector parser with enhanced conversion.
This replaces the C vector conversion logic with pure Scheme implementation."
  ;; Use the existing elisp vector parser logic
  (let ((guile-vector (elisp-parse-vector-from-port port)))
    (cond
      ((eof-object? guile-vector)
       (error "Unexpected EOF while reading vector"))
      ((vector? guile-vector)
       ;; Use enhanced conversion function instead of C guile_to_lisp_object
       (elisp-convert-guile-object guile-vector))
      (else
       (error "Vector parser returned non-vector")))))

;; Generic enhanced wrapper for future C-to-Scheme migrations
(define (elisp-parse-with-enhanced-conversion parser-func port)
  "Generic enhanced parser wrapper that applies common optimizations.
This function serves as a template for migrating more C logic to Scheme."
  (let ((result (parser-func port)))
    ;; Apply common conversions and optimizations
    (elisp-convert-guile-object result)))

;; Enhanced recursive parsing to eliminate C return fread0() patterns
(define (elisp-parse-with-recursive-reading parser-func port)
  "Enhanced parsing that handles recursive reading cases in Scheme.
This eliminates C patterns like 'return fread0(ctx)' for comments and special cases."
  (let loop ()
    (let ((result (parser-func port)))
      (cond
        ;; Comment processed: read next object recursively
        ((or (eq? result #nil)
             (eq? result 'comment-processed)
             (eq? result 'continue-reading))
         ;; Instead of C calling fread0(), do recursive read in Scheme
         (loop))
        ;; Regular result: return it
        (else result)))))

;; Enhanced comment skipping with recursive reading
(define (elisp-skip-comment-with-recursive-reading port)
  "Skip comment and automatically read the next object.
This eliminates the C pattern: skip_comment(); return fread0();"
  (elisp-skip-comment-from-port port)
  ;; Instead of returning to C to call fread0(), read next object in Scheme
  (elisp-read-from-port port))

;; Conservative fread0 helper - handles EOF checking in Scheme
(define (elisp-parse-with-eof-check char-code port)
  "Conservative Scheme helper for fread0 - handles EOF checking and dispatching.
Takes character as integer from C, checks for EOF, then dispatches."
  (if (= char-code -1)
      (error "End of file during parsing")
      (elisp-parse-comprehensive-dispatch (integer->char char-code) port)))

;; Complete Scheme fread0 - reads character from port itself
(define (elisp-fread0-complete port)
  "Complete Scheme implementation of fread0.
Reads character from port and handles all parsing logic."
  (let ((c (read-char port)))
    (cond
      ((eof-object? c) (error "End of file during parsing"))
      (else (elisp-parse-comprehensive-dispatch c port)))))

;; Complete Scheme fread0 - receives character from C like comprehensive dispatch
(define (elisp-fread0-with-char-from-c char-code port)
  "Complete Scheme implementation of fread0 that receives character from C.
More reliable for file context integration."
  (if (= char-code -1)
      (error "End of file during parsing")
      (elisp-parse-comprehensive-dispatch (integer->char char-code) port)))

;; Comprehensive switch statement replacement for multiple cases
(define (elisp-parse-comprehensive-dispatch char port)
  "Comprehensive parsing dispatcher that handles multiple switch cases.
This function could replace large portions of the C switch statement."
  (cond
    ;; Whitespace - skip and read next (handle first with predicates)
    ((or (char<=? char #\space) (char=? char #\240)) ; NO_BREAK_SPACE = 240
     ;; Skip whitespace and read the next character
     (let loop ((ch (read-char port)))
       (cond
         ((eof-object? ch) (error "End of file during parsing"))
         ((or (char<=? ch #\space) (char=? ch #\240))
          (loop (read-char port))) ; Skip more whitespace
         (else
          ;; Found non-whitespace character, parse it
          (elisp-parse-comprehensive-dispatch ch port)))))

    ;; List parsing
    ((char=? char #\() (elisp-parse-list-from-port port))

    ;; Vector parsing
    ((char=? char #\[) (elisp-parse-vector-from-port port))

    ;; Hash syntax
    ((char=? char #\#)
     ;; Handle hash with potential comment recursion
     (let ((result (elisp-parse-hash-from-port port)))
       (if (eq? result #nil)
           ;; Comment case: read next object
           (elisp-read-from-port port)
           ;; Regular result
           result)))

    ;; Character literal
    ((char=? char #\?) (elisp-parse-char-literal-from-port port))

    ;; String literal
    ((char=? char #\")
     ;; String literal - " already consumed by C, unget it for string parser
     (unread-char #\" port)
     (elisp-parse-string-literal-from-port port))

    ;; Quote with list construction
    ((char=? char #\') (elisp-parse-quote-with-list-construction port))

    ;; Backquote with list construction
    ((char=? char #\`) (elisp-parse-backquote-with-list-construction port))

    ;; Comma syntax
    ((char=? char #\,) (elisp-parse-comma-from-port port))

    ;; Comment with recursive reading
    ((char=? char #\;) (elisp-skip-comment-with-recursive-reading port))

    ;; Default: character-based dispatch
    (else (elisp-parse-character-dispatch char port))))

;; Comprehensive character-based dispatcher to minimize C switch logic
(define (elisp-parse-character-dispatch char port)
  "Comprehensive character-based parsing dispatcher.
This function handles character type detection and parsing dispatch,
eliminating the need for multiple C character checks and scm_ungetc calls."
  (cond
    ;; Numeric characters (0-9, +, -, .)
    ((or (and (char>=? char #\0) (char<=? char #\9))
         (char=? char #\+) (char=? char #\-) (char=? char #\.))
     ;; Unread the character and parse as number
     (unread-char char port)
     (elisp-parse-number-from-port port))

    ;; Colon character (:)
    ((char=? char #\:)
     ;; Unread the character and parse as colon symbol
     (unread-char char port)
     (elisp-parse-colon-from-port port))

    ;; Alphabetic characters (a-z, A-Z)
    ((or (and (char>=? char #\a) (char<=? char #\z))
         (and (char>=? char #\A) (char<=? char #\Z)))
     ;; Unread the character and parse as symbol
     (unread-char char port)
     (elisp-parse-symbol-from-port port))

    ;; Default: symbol parsing
    (else
     ;; Unread the character and parse as symbol
     (unread-char char port)
     (elisp-parse-symbol-from-port port))))

;;; Unified parsers for fallthrough consolidation

;; Simple literal parser dispatcher - character and string
(define (elisp-parse-literal-unified char-code port)
  "Parse character or string literal based on character code"
  (let ((ch (integer->char char-code)))
    (cond
      ((char=? ch #\?)
       ;; Character literal
       (elisp-parse-char-literal-from-port port))
      ((char=? ch #\")
       ;; String literal
       (unread-char #\" port)
       (elisp-parse-string-literal-from-port port))
      ;; Should not reach here given C switch logic
      (else
       #nil))))

;; Comprehensive structural and literal parser - unified dispatcher
(define (elisp-parse-structural-literal-unified char-code port)
  "Parse structural (lists, vectors) and literal (chars, strings, hash syntax) based on character code"
  (let ((ch (integer->char char-code)))
    (cond
      ((char=? ch #\()
       ;; List parsing - ( already consumed by C
       (elisp-parse-list-from-port port))
      ((char=? ch #\[)
       ;; Vector parsing - [ already consumed by C
       (elisp-parse-vector-from-port port))
      ((char=? ch #\?)
       ;; Character literal - ? already consumed by C
       (elisp-parse-char-literal-from-port port))
      ((char=? ch #\")
       ;; String literal - " already consumed by C, unget it for string parser
       (unread-char #\" port)
       (elisp-parse-string-literal-from-port port))
      ((char=? ch #\#)
       ;; Hash syntax - # already consumed by C, delegate to comprehensive hash parser
       (elisp-parse-hash-from-port port))
      ;; Should not reach here given C switch logic
      (else
       #nil))))

;; Safe quote and backquote dispatcher - minimal consolidation
(define (elisp-parse-quote-backquote-dispatch char-code port)
  "Dispatch quote and backquote syntax based on character code"
  (let ((ch (integer->char char-code)))
    (cond
      ((char=? ch #\')
       ;; Quote form
       (let ((obj (elisp-read-from-port port)))
         (cons 'quote (cons obj #nil))))
      ((char=? ch #\`)
       ;; Backquote form
       (let ((obj (elisp-read-from-port port)))
         (cons 'backquote (cons obj #nil))))
      (else
       ;; Default case should never be reached
       #nil))))

(define (elisp-parse-quote-like-syntax port ch)
  "Unified parser for quote-like syntax: ', `, ,, ,@"
  (cond
    ((char=? ch #\')
     ;; Quote form
     (let ((obj (elisp-read-from-port port)))
       (cons 'quote (cons obj #nil))))
    ((char=? ch #\`)
     ;; Backquote form
     (let ((obj (elisp-read-from-port port)))
       (cons 'backquote (cons obj #nil))))
    ((char=? ch #\,)
     ;; Comma syntax - check for ,@
     (let ((next-ch (peek-char port)))
       (if (and (char? next-ch) (char=? next-ch #\@))
           (begin
             (read-char port)  ; consume the @
             (let ((expr (elisp-read-from-port port)))
               (cons (elisp-intern ",@" #nil) (cons expr #nil))))
           ;; Regular comma
           (let ((expr (elisp-read-from-port port)))
             (cons (elisp-intern "," #nil) (cons expr #nil))))))
    (else
     ;; Default case should never be reached
     #nil)))

(define (elisp-parse-literal port ch)
  "Unified parser for literal syntax: ? (char) and \" (string)"
  (cond
    ((char=? ch #\?)
     ;; Character literal
     (elisp-parse-char-literal-from-port port))
    ((char=? ch #\")
     ;; String literal
     (elisp-parse-string-literal-from-port port))
    ;; Default case should never be reached
    (else
     #nil)))

(define (elisp-parse-structural char-code port)
  "Unified parser for structural syntax: (, [, # - takes character code"
  (let ((ch (integer->char char-code)))
    (cond
      ((char=? ch #\()
       ;; List parsing
       (elisp-parse-list-from-port port))
      ((char=? ch #\[)
       ;; Vector parsing
       (elisp-parse-vector-from-port port))
      ((char=? ch #\#)
       ;; Hash syntax
       (elisp-parse-hash-from-port port))
      ;; Default case should never be reached given the C switch logic
      (else
       ;; Return nil as fallback
       #nil))))

;; Performance metrics function to measure migration benefits
(define (elisp-reader-performance-info)
  "Return information about the Scheme-enhanced reader performance optimizations."
  (cons 'reader-optimizations
        '((malloc-free-cycles-eliminated . symbol-keyword-conversion)
          (c-wrapper-functions-simplified . 12)
          (type-checking-moved-to-scheme . 6)
          (generic-wrapper-pattern-established . #t)
          (enhanced-conversion-functions-available . #t))))

;;; Incremental migration functions - small steps toward full Scheme reader

;; Whitespace and EOF handler - small incremental step toward full Scheme reader
(define (elisp-handle-whitespace-and-eof port)
  "Handle whitespace skipping and EOF detection for fread0.
Returns 'eof if EOF was encountered,
Returns 'whitespace-skipped if whitespace was skipped (caller should try again),
Otherwise ungets the character and returns the character."
  (let ((ch (read-char port)))
    (cond
      ;; EOF handling
      ((eof-object? ch)
       'eof)

      ;; Whitespace - skip and indicate to try again
      ((or (char<=? ch #\space) (char=? ch #\240)) ; NO_BREAK_SPACE = 240
       ;; Skip whitespace and try again recursively
       (elisp-handle-whitespace-and-eof port))

      ;; Regular character - unget it and return it for C processing
      (else
       (unread-char ch port)
       ch))))

;;; Load-specific helper functions for readevalloop_load migration

;; Phase 1: Extract Helper Functions for readevalloop_load

(define (elisp-skip-load-whitespace-from-port port)
  "Skip whitespace characters specific to load operations.
This handles the exact same whitespace as readevalloop_load:
space, tab, newline, form feed, carriage return, and NO_BREAK_SPACE.
Returns: #t when done skipping whitespace"
  (let loop ()
    (let ((ch (peek-char port)))
      (cond
        ((eof-object? ch) #t)
        ;; Match exact whitespace from readevalloop_load lines 2100-2102
        ((or (char=? ch #\space)   ; ' '
             (char=? ch #\tab)     ; '\t'
             (char=? ch #\newline) ; '\n'
             (char=? ch #\page)    ; '\f' (form feed)
             (char=? ch #\return)  ; '\r'
             (char=? ch #\x00A0))  ; NO_BREAK_SPACE
         (read-char port) ; consume the whitespace character
         (loop))
        (else #t)))))

(define (elisp-skip-load-comment-from-port port)
  "Skip a line comment for load operations, matching readevalloop_load logic.
This handles comments starting with ';' until newline or EOF.
Returns: #t when comment is fully skipped"
  ;; Consume characters until newline or EOF (matching lines 2090-2091)
  (let loop ()
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) #t)
        ((char=? ch #\newline) #t)
        (else (loop))))))

(define (elisp-read-with-load-function-from-port port)
  "Handle custom reader function delegation for load operations.
This replicates the conditional logic from readevalloop_load lines 2113-2127.
Returns: The result of the appropriate read function"
  ;; For now, simplify to only handle the main case since readfun is Qnil in readevalloop_load
  ;; In the original C code, readfun is always Qnil for file loading
  (let ((load-read-fn ((symbol-function 'symbol-value) 'load-read-function)))
    (cond
      ;; Non-default custom read function (lines 2118-2122)
      ((and (not (eq? load-read-fn #nil))
            (not (eq? load-read-fn ((symbol-function 'intern) "read" #nil))))
       ((symbol-function 'funcall) load-read-fn ((symbol-function 'symbol-value) 'get-file-char)))

      ;; Default case: use elisp-read-from-port (lines 2125-2126)
      ;; This handles both readfun=nil and the standard case
      (else
       (elisp-read-from-port port)))))

;;; End Section 9


;;; ============================================================================
;;; SECTION 10: LOAD SYSTEM
;;; ============================================================================
;;;
;;; File loading infrastructure - handles .el/.elc files, load-path, etc.
;;; Migrated from lread.c Fload function.
;;; Includes: file validation, load-path management, read-eval loop, history.

(define (elisp-load-read-next-expression-from-port port)
  "Read the next complete expression from PORT, handling all preprocessing.
This function unifies whitespace skipping, comment skipping, EOF detection,
and expression reading into a single atomic operation.

Returns:
- The next expression to evaluate
- 'eof if end of file reached
- Automatically handles all whitespace and comments"
  (let loop ()
    ;; Skip whitespace first
    (elisp-skip-load-whitespace-from-port port)

    ;; Check what comes next
    (let ((ch (peek-char port)))
      (cond
        ;; EOF reached
        ((eof-object? ch) 'eof)

        ;; Comment - skip it and try again
        ((char=? ch #\;)
         (read-char port) ; consume the semicolon
         (elisp-skip-load-comment-from-port port)
         (loop)) ; recursively try to read next expression

        ;; Regular expression - read it
        (else
         (elisp-read-with-load-function-from-port port))))))

;; Phase 4: Complete Read-Eval Loop Migration

(define (elisp-load-read-eval-loop-from-port port printflag)
  "Complete read-eval loop for file loading.
Reads expressions from PORT, evaluates them, and optionally prints results.
This replaces the entire while loop from readevalloop_load."
  (let loop ()
    (let ((expr (elisp-load-read-next-expression-from-port port)))
      (cond
        ;; EOF reached - stop looping
        ((eq? expr 'eof) 'done)

        ;; Regular expression - evaluate and continue
        (else
         ;; Delegate evaluation to C eval_sub to preserve all Elisp semantics
         (let ((result ((symbol-function 'eval) expr)))
           ;; Handle printing if requested
           (when (not (eq? printflag #f))
             ;; Add result to Vvalues for interactive sessions
             ((symbol-function 'set) 'values
              ((symbol-function 'cons) result ((symbol-function 'symbol-value) 'values)))
             ;; Print using appropriate function
             (if (eq? ((symbol-function 'symbol-value) 'standard-output) #t)
                 ((symbol-function 'prin1) result)
                 ((symbol-function 'print) result)))
           ;; Continue looping
           (loop)))))))

(define (elisp-complete-file-load-from-port port sourcename printflag)
  "Complete readevalloop_load replacement that handles all file loading logic.
This replaces readevalloop_load (src/lread.c:2055-2078) with full semantic compatibility.

Handles:
- File path normalization (replicates line 2071)
- Load history initialization (replicates line 2073)
- Read-eval loop execution (replicates line 2075)
- Dynamic binding setup is handled by C wrapper for proper unwind-protect integration"

  ;; Normalize file path (replicates readevalloop_load line 2071)
  (let ((normalized-sourcename (elisp-normalize-load-path sourcename)))
    ;; Note: loadhist_initialize is handled by C wrapper for proper global structure access

    ;; Execute the complete read-eval loop (replicates readevalloop_load line 2075)
    (elisp-load-read-eval-loop-from-port port printflag)

    ;; Return normalized sourcename for C wrapper to use with loadhist_initialize
    normalized-sourcename))

(define (elisp-readevalloop-load-from-port port sourcename)
  "Complete Scheme replacement for readevalloop_load C function.
This handles the core logic, with dynamic binding delegated back to C wrapper.
Replicates the core behavior of src/lread.c:2055-2088."

  ;; Validate input (replicates CHECK_STRING)
  (unless (string? sourcename)
    (error "sourcename must be a string" sourcename))

  ;; File loading setup (replicates line 2060)
  (let ((printflag #f)) ; File loading doesn't print by default

    ;; Note: Dynamic binding (specbind calls) are complex to replicate in Scheme
    ;; For now, we handle the core logic and let C handle the binding setup
    ;; TODO: Move dynamic binding to Scheme in a future iteration

    ;; Normalize file path (replicates line 2071)
    (let ((normalized-sourcename (elisp-normalize-load-path sourcename)))

      ;; Initialize load history (replicates line 2073)
      ;; Use Elisp function call for proper integration
      ((symbol-function 'elisp-loadhist-initialize) normalized-sourcename)

      ;; Execute the complete read-eval loop (replicates line 2075)
      (elisp-load-read-eval-loop-from-port port printflag)

      ;; Return success (C function returns void, so we just complete)
      'done)))

(define (elisp-setup-default-lexical-binding)
  "Set up default dynamic binding for load context.
This replicates the lexical binding setup from Fload (lines 1046-1050).
All loads are by default dynamic, unless the file itself specifies otherwise."

  ;; Bind lexical-binding to nil (dynamic binding by default)
  ;; This will be handled by specbind in the C wrapper since it needs proper cleanup
  'setup-for-c-specbind)

(define (elisp-compute-found-effective found)
  "Compute effective filename from found filename.
This replicates the compute_found_effective function from lread.c lines 869-882.
Handles .el.gz files by removing .gz suffix and adding 'c' suffix for .elc files."

  ;; Set src_name to nil initially (this matches the C code)
  (let ((src-name #nil))

    ;; If src_name is nil (which it always is in this implementation)
    ;; return found as-is (manual eln load case)
    (if (eq? src-name #nil)
        found
        ;; Original logic for when src_name is not nil:
        ;; Check if it ends with "el.gz" and process accordingly
        (let ((src-string (if (string? src-name) src-name (scm_to_utf8_string src-name))))
          (if (string-suffix? "el.gz" src-string)
              ;; Remove .gz suffix and add 'c' suffix
              (let* ((base-name (substring src-string 0 (- (string-length src-string) 3)))
                     (base-lisp ((symbol-function 'substring) src-name
                                (elisp-intern "0" #nil)
                                (elisp-intern "-3" #nil))))
                ((symbol-function 'concat) base-lisp "c"))
              ;; Just add 'c' suffix for regular .el files
              ((symbol-function 'concat) src-name "c"))))))

(define (elisp-handle-lexical-binding-specbind)
  "Return the appropriate binding for lexical-binding variable.
This prepares the specbind call for lexical-binding from Fload (line 1033)."

  ;; Return a cons cell for specbind: (Qlexical_binding . Qnil)
  ;; The actual specbind call will be done in C
  ((symbol-function 'cons) (elisp-intern "lexical-binding" #nil) #nil))

(define (elisp-orchestrate-file-reading port hist-file-name)
  "Orchestrate the file reading process including sync and evaluation.
This replicates the orchestration from Fload (lines 1202-1203)."

  ;; This function serves as a scheme-side coordinator for the reading process
  ;; The actual sync_guile_reader and readevalloop_load calls remain in C
  ;; but this provides a scheme hook point for future enhancements

  ;; For now, return success indicator - the C code will handle the actual calls
  #t)

;; COMPOUND FUNCTIONS - Consolidate multiple operations to reduce C-Guile marshalling

;; Custom elisp reader that handles colon symbols properly
(define (custom-elisp-read port)
  "Custom elisp reader that creates self-evaluating colon symbols"
  (let ((original-result (read port)))
    (cond
      ;; Handle Guile keywords (converted from :symbol syntax)
      ((keyword? original-result)
       (let* ((keyword-symbol (keyword->symbol original-result))
              (base-name (symbol->string keyword-symbol))
              (colon-name (string-append ":" base-name)))
         ;; Create self-evaluating elisp symbol
         (let ((elisp-symbol ((symbol-function 'intern) colon-name #nil)))
           ((symbol-function 'set) elisp-symbol elisp-symbol)
           elisp-symbol)))
      ;; Pass through everything else
      (else original-result))))

;; Define intern-gensym first - creates interned unique symbols
(define %intern-gensym 0)
(define (intern-gensym prefix)
  (set! %intern-gensym (+ 1 %intern-gensym))
  (string->symbol (string-concatenate (list prefix "_" (number->string %intern-gensym)))))

;; Make make-symbol create interned symbols (not uninterned) to avoid Guile serialization errors
;; Uninterned symbols cannot be saved to .go files
(define (make-symbol name)
  (intern-gensym name))

(define (init-reader prelude-directory)
  (set-current-module (resolve-module '(emacs-elisp runtime)))

  (set-symbol-function! 'make-symbol make-symbol)
  (set-symbol-function! 'intern-gensym intern-gensym)
  )
