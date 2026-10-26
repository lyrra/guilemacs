;;; Guilemacs Lisp - File Loading Infrastructure
;;;
;;; Module: (emacs loader)
;;; Purpose: File loading infrastructure for Elisp files
;;; Loading: via use-modules in load.scm

(define-module (emacs loader)
  #:use-module (system base language)
  #:use-module ((system base compile)
                ;; M60 imp-3: load-elisp calls `compiled-file-name', which
                ;; was UNBOUND in this module (MEASURED).  The M55 imp-4
                ;; comment below assumed a plain `guile' process never
                ;; reaches the compiled branch; the split registration
                ;; makes the language findable, so the import is needed.
                #:select (compile compile-file compiled-file-name))
  ;; M60 imp-7 fix (cr.org F3): `remove' drops a shadowed macro entry.
  #:use-module ((srfi srfi-1) #:select (count any remove))
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs utils)
  ;; M60 imp-10 -- row 29: the comparison and arithmetic cells, plus
  ;; `length'.  Every name already has a pure-Scheme definition, so this
  ;; row adds IMPORTS and GUARDED INSTALLS only.  The 2 modules import
  ;; `(emacs-elisp runtime)' and nothing from `(emacs loader)', so the
  ;; module graph stays acyclic.
  #:use-module ((emacs types)
                #:select (elisp-eq elisp-eql elisp-equal elisp-null
                           ;; M60 imp-15 -- row 32: 1 SRFI-69 table IS
                           ;; the elisp hash table, so the existing
                           ;; predicate of types.scm :444 is the cell.
                           elisp-hash-table-p
                           ;; M60 imp-18 -- row 35: the identity of
                           ;; types.scm :426, guarded install below.
                           elisp-bare-symbol))
  #:use-module ((emacs numbers)
                #:select (elisp-+ elisp-- elisp-* elisp-/
                           elisp-= elisp-< elisp->
                           elisp-1+ elisp-1-))
  #:use-module ((emacs sequences) #:select (elisp-append elisp-length))
  ;; M60 imp-5: the elisp `load' protocol applies `string-suffix-p'
  ;; (loader.scm :257).  In a plain `guile' process that cell is EMPTY, so
  ;; `init-loader' installs the existing pure-Scheme definition.  The
  ;; import is `#:select' only: (emacs strings) does not use (emacs
  ;; loader), so the module graph stays acyclic.
  #:use-module ((emacs strings) #:select (elisp-string-suffix-p))
  #:use-module ((emacs list) #:select (elisp-car elisp-cdr))
  #:use-module (emacs reader)
  #:export (
    init-loader
    elisp-call-load-source-file-function
    elisp-complete-file-load-from-port
    elisp-complete-filename?
    elisp-compute-effective-filename
    elisp-compute-found-effective
    elisp-compute-hist-file-name
    elisp-count-recursive-loads
    elisp-detect-lexical-binding
    elisp-determine-load-action
    elisp-format-load-message
    elisp-handle-file-open-error
    elisp-handle-lexical-binding-specbind
    elisp-handle-loads-in-progress
    elisp-handle-user-init-file
    elisp-loadhist-initialize
    elisp-load-read-eval-loop-from-port
    elisp-load-read-next-expression-from-port
    elisp-normalize-load-path
    elisp-orchestrate-file-reading
    elisp-prepare-load-bindings
    elisp-prepare-module-loading
    elisp-prepare-openp-call
    elisp-process-load-file-path
    elisp-readevalloop-load-from-port
    elisp-read-next-expression-from-port
    elisp-eval-loop-from-port
    elisp-eval-region-from-string
    elisp-eval-buffer-from-string
    elisp-return-load-success
    elisp-setup-default-lexical-binding
    elisp-setup-file-descriptor-protection
    elisp-setup-load-environment
    elisp-setup-port-input
    elisp-should-close-fd
    elisp-show-load-message
    elisp-validate-and-check-handler
    elisp-validate-file-descriptor
    elisp-validate-load-file
    elisp-load
    search-elisp-load-path
    load-elisp
    load-elisp-full
    elisp-autoload-do-load
    file-being-loaded?
  ))

;;;
;;; All loader function implementations below
;;;

;;; Track files currently being loaded to prevent circular require loops
;;; This is a fluid/parameter that holds a list of file paths currently being loaded
(define *files-being-loaded* (make-parameter '()))

;;;
;;; Read-Eval Loop Functions
;;;

(define (elisp-load-read-next-expression-from-port port)
  "Read the next complete expression from PORT, handling all preprocessing.
This function unifies whitespace skipping, comment skipping, EOF detection,
and expression reading into a single atomic operation.

Returns:
- The next expression to evaluate
- 'eof if end of file reached
- Automatically handles all whitespace and comments"
  (let loop ()
    (elisp-skip-load-whitespace-from-port port)
    (let ((ch (peek-char port)))
      (cond
        ((eof-object? ch) 'eof)
        ((char=? ch #\;)
         (read-char port)
         (elisp-skip-load-comment-from-port port)
         (loop))
        (else
         (elisp-read-with-load-function-from-port port))))))

(define (elisp-load-read-eval-loop-from-port port printflag)
  "Complete read-eval loop for file loading.
Reads expressions from PORT, evaluates them, and optionally prints results.
This replaces the entire while loop from readevalloop_load."
  (let loop ()
    (let ((expr (elisp-load-read-next-expression-from-port port)))
      (cond
        ((eq? expr 'eof) 'done)
        (else
         (let ((result ((symbol-function 'eval) expr)))
           (when (not (eq? printflag #f))
             ((symbol-function 'set) 'values
              ((symbol-function 'cons) result ((symbol-function 'symbol-value) 'values)))
             (if (eq? ((symbol-function 'symbol-value) 'standard-output) #t)
                 ((symbol-function 'prin1) result)
                 ((symbol-function 'print) result)))
           (loop)))))))

(define (elisp-normalize-load-path sourcename)
  "Normalize the file path for loading, making it absolute if needed.
This replicates the C logic from readevalloop_load lines 2077-2080."
  (if (not (eq? ((symbol-function 'file-name-absolute-p) sourcename) #nil))
      ((symbol-function 'expand-file-name) sourcename #nil)
      sourcename))

(define (elisp-complete-file-load-from-port port sourcename printflag)
  "Complete readevalloop_load replacement that handles all file loading logic.
This replaces readevalloop_load (src/lread.c:2055-2078) with full semantic compatibility.

Handles:
- File path normalization (replicates line 2071)
- Load history initialization (replicates line 2073)
- Read-eval loop execution (replicates line 2075)
- Dynamic binding setup is handled by C wrapper for proper unwind-protect integration"
  (let ((normalized-sourcename (elisp-normalize-load-path sourcename)))
    (elisp-load-read-eval-loop-from-port port printflag)
    normalized-sourcename))

(define (elisp-readevalloop-load-from-port port sourcename)
  "Complete Scheme replacement for readevalloop_load C function.
This handles the core logic, with dynamic binding delegated back to C wrapper.
Replicates the core behavior of src/lread.c:2055-2088."
  (unless (string? sourcename)
    (error "sourcename must be a string" sourcename))
  (let ((printflag #f))
    (let ((normalized-sourcename (elisp-normalize-load-path sourcename)))
      ((symbol-function 'elisp-loadhist-initialize) normalized-sourcename)
      (elisp-load-read-eval-loop-from-port port printflag)
      'done)))

;;;
;;; Buffer/Region Evaluation Functions
;;;
;;; These functions implement eval-region and eval-buffer by creating
;;; string ports from buffer contents and feeding them to the reader.
;;;

(define (elisp-read-next-expression-from-port port readfun)
  "Read the next expression from PORT for eval-region/eval-buffer.
Uses READFUN if provided, otherwise uses the standard elisp reader.
Returns 'eof if end of input reached."
  (let loop ()
    ;; Skip whitespace
    (let skip-ws ()
      (let ((ch (peek-char port)))
        (when (and (not (eof-object? ch))
                   (or (char=? ch #\space)
                       (char=? ch #\tab)
                       (char=? ch #\newline)
                       (char=? ch #\page)
                       (char=? ch #\return)
                       (char=? ch #\xa0)))  ; NO_BREAK_SPACE
          (read-char port)
          (skip-ws))))
    (let ((ch (peek-char port)))
      (cond
        ((eof-object? ch) 'eof)
        ;; Skip line comments
        ((char=? ch #\;)
         (read-char port)
         (let skip-comment ()
           (let ((c (read-char port)))
             (unless (or (eof-object? c) (char=? c #\newline))
               (skip-comment))))
         (loop))
        (else
         ;; Read expression using readfun or standard reader
         (if (and readfun (not (eq? readfun #nil)))
             ;; Call the custom read function
             ;; It expects a "stream" which in Emacs is the buffer
             ;; For now, we read using standard reader
             ;; TODO: properly support custom readfun
             (elisp-read-from-port port)
             (elisp-read-from-port port)))))))

(define (elisp-eval-loop-from-port port printflag readfun)
  "Read-eval loop for eval-region/eval-buffer.
Reads expressions from PORT, evaluates them, and optionally prints results."
  (let loop ()
    (let ((expr (elisp-read-next-expression-from-port port readfun)))
      (cond
        ((eq? expr 'eof) #nil)
        (else
         (let ((result ((symbol-function 'eval) expr)))
           (when (and printflag (not (eq? printflag #nil)))
             ;; Add to values list
             ((symbol-function 'set) 'values
              ((symbol-function 'cons) result
               ((symbol-function 'symbol-value) 'values)))
             ;; Print result
             (if (eq? ((symbol-function 'symbol-value) 'standard-output) #t)
                 ((symbol-function 'prin1) result #nil #nil)
                 ((symbol-function 'print) result #nil)))
           (loop)))))))

(define (elisp-eval-region-from-string content printflag readfun)
  "Scheme implementation of eval-region read-eval loop.
CONTENT is the string content to evaluate.
PRINTFLAG controls output, READFUN is optional custom read function.
Called from C after buffer content has been extracted."
  (let ((port (open-input-string content)))
    (elisp-eval-loop-from-port port printflag readfun)
    #nil))

(define (elisp-eval-buffer-from-string content printflag)
  "Scheme implementation of eval-buffer read-eval loop.
CONTENT is the buffer content as a string.
PRINTFLAG controls output.
Called from C after buffer content has been extracted."
  (let ((port (open-input-string content)))
    (elisp-eval-loop-from-port port printflag #nil)
    #nil))

;;;
;;; File Path Processing
;;;

(define (elisp-process-load-file-path file nosuffix must-suffix)
  "Process file path and determine suffixes for loading.
This replicates the file path processing logic from Fload (lines 979-1020).

Returns: (file-to-search . suffixes-list)
- file-to-search: the file name to search for
- suffixes-list: list of suffixes to try, or #nil"
  (when (= (elisp-string-length-for-load file) 0)
    (error "Cannot load empty filename"))
  (let ((suffixes #nil))
    (unless (eq? must-suffix #nil)
      (when (or ((symbol-function 'string-suffix-p) ".el" file #t))
        (set! must-suffix #nil))
      (unless (eq? ((symbol-function 'file-name-directory) file) #nil)
        (set! must-suffix #nil)))
    (cond
      ((not (eq? nosuffix #nil))
       (set! suffixes #nil))
      (else
       (set! suffixes ((symbol-function 'get-load-suffixes)))
       (when (eq? must-suffix #nil)
         (set! suffixes ((symbol-function 'append) suffixes
                        ((symbol-function 'symbol-value)
                         (elisp-intern "load-file-rep-suffixes" #nil)))))))
    (cons file suffixes)))

;;;
;;; Load Message Formatting
;;;

(define (elisp-format-load-message file is-module is-native-elisp compiled newer loading-p)
  "Format loading messages for different file types.
This replicates the message formatting logic from Fload (lines 1153-1166, 1210-1223).

- loading-p: #t for 'Loading...' messages, #f for '...done' messages"
  (let ((base-msg
         (cond
           (is-module
            (if loading-p "Loading %s (module)..." "Loading %s (module)...done"))
           (is-native-elisp
            (if loading-p "Loading %s (native compiled elisp)..."
                          "Loading %s (native compiled elisp)...done"))
           ((not compiled)
            (if loading-p "Loading %s (source)..." "Loading %s (source)...done"))
           (newer
            (if loading-p "Loading %s (compiled; note, source file is newer)..."
                          "Loading %s (compiled; note, source file is newer)...done"))
           (else
            (if loading-p "Loading %s..." "Loading %s...done")))))
    ((symbol-function 'message) base-msg file)))

(define (elisp-show-load-message file is-module is-native-elisp compiled newer loading-p nomessage force-load-messages noninteractive-p)
  "Display loading messages with proper conditional logic.
This replicates the message display logic from Fload (lines 1133-1146, 1190-1203)."
  (let ((should-show-loading (or (eq? nomessage #nil) force-load-messages))
        (should-show-done (and (not noninteractive-p)
                              (or (eq? nomessage #nil) force-load-messages))))
    (when (if loading-p should-show-loading should-show-done)
      (let ((base-msg
             (cond
               (is-module
                (if loading-p "Loading %s (module)..." "Loading %s (module)...done"))
               (is-native-elisp
                (if loading-p "Loading %s (native compiled elisp)..."
                              "Loading %s (native compiled elisp)...done"))
               ((not compiled)
                (if loading-p "Loading %s (source)..." "Loading %s (source)...done"))
               (newer
                (if loading-p "Loading %s (compiled; note, source file is newer)..."
                              "Loading %s (compiled; note, source file is newer)...done"))
               (else
                (if loading-p "Loading %s..." "Loading %s...done")))))
        ((symbol-function 'message) base-msg file)))))

;;;
;;; File Name Computation
;;;

(define (elisp-compute-effective-filename found is-native-elisp)
  "Compute effective filename for loading.
  This replicates the found_eff computation from Fload lines 1040-1043."

  (if is-native-elisp
      ;; For native elisp, compute the effective name
      ((symbol-function 'compute-found-effective) found)
      ;; For regular files, use found as-is
      found))

(define (elisp-compute-hist-file-name file found-eff purify-flag)
  "Compute the history file name for load-history.
This replicates the hist_file_name computation from Fload (lines 1063-1067)."
  (if (not (eq? purify-flag #nil))
      ((symbol-function 'concat)
       ((symbol-function 'file-name-directory) file)
       ((symbol-function 'file-name-nondirectory) found-eff))
      found-eff))

(define (elisp-compute-found-effective found)
  "Compute effective filename from found filename.
This replicates the compute_found_effective function from lread.c lines 869-882.
Handles .el.gz files by removing .gz suffix and adding 'c' suffix for .elc files."
  (let ((src-name #nil))
    (if (eq? src-name #nil)
        found
        (let ((src-string (if (string? src-name) src-name (scm_to_utf8_string src-name))))
          (if (string-suffix? "el.gz" src-string)
              (let* ((base-name (substring src-string 0 (- (string-length src-string) 3)))
                     (base-lisp ((symbol-function 'substring) src-name
                                (elisp-intern "0" #nil)
                                (elisp-intern "-3" #nil))))
                ((symbol-function 'concat) base-lisp "c"))
              ((symbol-function 'concat) src-name "c"))))))

;;;
;;; Recursive Load Detection
;;;

(define (elisp-count-recursive-loads found loads-in-progress-list)
  "Count how many times a file appears in the loads-in-progress list.
This replicates the counting logic from Fload recursive load detection.
Signals an error if more than 3 recursive loads are detected."
  (let ((load-count 0))
    (let loop ((tem loads-in-progress-list))
      (when (not (eq? tem #nil))
        (when (not (eq? ((symbol-function 'equal) found ((symbol-function 'car) tem)) #nil))
          (set! load-count (+ load-count 1)))
        (loop ((symbol-function 'cdr) tem))))
    (when (> load-count 3)
      ((symbol-function 'signal) (elisp-intern "error" #nil)
       ((symbol-function 'list) "Recursive load"
        ((symbol-function 'cons) found loads-in-progress-list))))
    load-count))

;;;
;;; Load Environment Setup
;;;

(define (elisp-setup-default-lexical-binding)
  "Set up default dynamic binding for load context.
This replicates the lexical binding setup from Fload (lines 1046-1050).
All loads are by default dynamic, unless the file itself specifies otherwise."
  'setup-for-c-specbind)

(define (elisp-call-load-source-file-function load-source-file-function found hist-file-name noerror nomessage force-load-messages)
  "Call the load-source-file-function with properly converted arguments.
This replicates the call4 logic from Fload (lines 1065-1067)."
  (let ((error-arg (if (eq? noerror #nil) #nil #t))
        (message-arg (if (or (eq? nomessage #nil) force-load-messages) #nil #t)))
    ((symbol-function 'funcall) load-source-file-function found hist-file-name error-arg message-arg)))

;;;
;;; File Validation
;;;

(define (elisp-string-length-for-load file)
  "Length of FILE for the empty-filename check in `elisp-validate-load-file'.
FIX-20261011-guilemacs: a plain `guile' process had no Emacs C core, so
the elisp `length' cell was EMPTY and the old `((symbol-function 'length)
file)' apply raised `wrong-type-arg'.  M60 imp-10 (row 29) installs
`length' from (emacs sequences), so after `init-loader' the cell is BOUND
on the plain path AND on the full-Emacs path (measured: (elisp-length
\"abc\") gives 3).
The `string-length' branch is UNREACHED on the `init-loader' path only.
cr.org F6: it is NOT dead for every caller -- a caller that uses
(emacs loader) WITHOUT `init-loader' still has an EMPTY `length' cell
(NOT measured; written as a limit, not as a fact).  The branch and the
FIX marker stay, so the FIX-marker count stays 9; a later row may delete
both and move the count to 8.  No C delta."
  (if (symbol-fbound? 'length)
      ((symbol-function 'length) file)
      (string-length file)))

(define (elisp-validate-load-file file)
  "Validate file argument for loading.
This replicates the validation logic from Fload (lines 966, 976-977).
Returns #t if valid, signals error if invalid."
  (unless (string? file)
    ((symbol-function 'signal) (elisp-intern "wrong-type-argument" #nil)
     ((symbol-function 'list) (elisp-intern "stringp" #nil) file)))
  (when (= (elisp-string-length-for-load file) 0)
    ((symbol-function 'signal) (elisp-intern "file-error" #nil)
     ((symbol-function 'list) "Cannot load empty filename")))
  #t)

(define (elisp-complete-filename? pathname)
  "Check if pathname is a complete filename.
This replicates the complete_filename_p function from lread.c lines 1258-1265.
Returns #t if pathname starts with directory separator or is a full Windows path."
  (let* ((path-string (if (string? pathname) pathname (scm_to_utf8_string pathname)))
         (path-length (string-length path-string)))
    (if (= path-length 0)
        #f
        (or
         ;; Check if starts with directory separator (Unix: /, Windows: \ or /)
         (or (char=? (string-ref path-string 0) #\/)
             (char=? (string-ref path-string 0) #\\))
         ;; Check for Windows drive letter format (C:\)
         (and (> path-length 2)
              (char=? (string-ref path-string 1) #\:)
              (or (char=? (string-ref path-string 2) #\/)
                  (char=? (string-ref path-string 2) #\\)))))))

;;;
;;; Load History Management
;;;

(define (elisp-loadhist-initialize filename)
  "Initialize load history for filename.
This replicates the loadhist_initialize function from lread.c lines 877-882.
Validates filename and sets up current-load-list binding."
  (unless (or (string? filename) (eq? filename #nil))
    ((symbol-function 'error) "filename must be string or nil"))
  ((symbol-function 'cons) filename #nil))

(define (elisp-handle-user-init-file found)
  "Handle user init file detection logic.
This replicates the user init file logic from Fload (lines 1002-1003).
Returns the value that should be assigned to Vuser_init_file."
  (if (eq? ((symbol-function 'symbol-value) (elisp-intern "user-init-file" #nil))
           ((symbol-function 'symbol-value) (elisp-intern "t" #nil)))
      found
      ((symbol-function 'symbol-value) (elisp-intern "user-init-file" #nil))))

(define (elisp-prepare-module-loading found)
  "Prepare for module loading by initializing load history.
This replicates the module loading preparation from Fload (lines 1176-1178)."
  ((symbol-function 'loadhist-initialize) found))

(define (elisp-prepare-load-bindings hist-file-name found)
  "Prepare all dynamic bindings for load operation.
  This replicates the specbind calls from Fload lines 1158-1161.
  Returns list of (symbol . value) pairs for C to bind."

  (list
   (cons 'load-file-name hist-file-name)
   (cons 'load-true-file-name found)
   (cons 'inhibit-file-name-operation #nil)
   (cons 'load-in-progress #t)))

;;;
;;; Binding Management
;;;

(define (elisp-handle-lexical-binding-specbind)
  "Return the appropriate binding for lexical-binding variable.
This prepares the specbind call for lexical-binding from Fload (line 1033)."
  ((symbol-function 'cons) (elisp-intern "lexical-binding" #nil) #nil))

;;;
;;; File Operations
;;;

(define (elisp-orchestrate-file-reading port hist-file-name)
  "Orchestrate the file reading process including sync and evaluation.
This replicates the orchestration from Fload (lines 1202-1203)."
  #t)

(define (elisp-handle-file-open-error fd noerror file)
  "Handle file opening errors and determine response.
This replicates the error handling from Fload (lines 993-999).
Returns: 'continue if should continue, 'return-nil if should return nil."
  (if (< fd 0)
      (if (eq? noerror #nil)
          ;; If noerror is nil, we should signal an error (handled in C)
          'signal-error
          ;; If noerror is non-nil, return nil quietly
          'return-nil)
      ;; File opened successfully, continue
      'continue))

(define (elisp-should-close-fd is-module is-native-elisp fd-valid)
  "Determine if file descriptor should be closed.
  This replicates the close logic from Fload lines 1089-1097."

  (and (not is-module)
       (not is-native-elisp)
       fd-valid))

(define (elisp-setup-file-descriptor-protection fd)
  "Determine if file descriptor needs unwind protection.
This replicates the unwind protection logic from Fload (lines 1008-1011).
Returns: #t if protection should be set up, #f otherwise."
  (>= fd 0))

(define (elisp-validate-file-descriptor fd-valid)
  "Validate file descriptor state.
  This replicates the errno setting from Fload lines 1078-1081.
  Returns validation result: 'valid or 'invalid."

  (if fd-valid
      'valid
      'invalid))

(define (elisp-prepare-openp-call path-result)
  "Prepare parameters for openp function call.
This replicates the openp call preparation from Fload (lines 985-991).
Returns: (processed-file . suffixes) pair for openp call."
  path-result)

(define (elisp-handle-loads-in-progress found loads-in-progress)
  "Prepare loads-in-progress list update.
This extends the recursive load handling from Fload (lines 1027-1029).
Returns: the new value for loads-in-progress list."
  ((symbol-function 'cons) found loads-in-progress))

(define (elisp-load-with-match-data-protection file noerror nomessage nosuffix must-suffix)
  "Load file with match data protection.
  This replicates the save_match_data_load wrapper function."
  ;; Call the main load function - C will handle the match data protection
  ((symbol-function 'load) file noerror nomessage nosuffix must-suffix))

(define (file-being-loaded? autoload-file)
  "Check if autoload-file (base name like 'gnus-sum') matches any file in *files-being-loaded*.
Returns #t if the file is currently being loaded (circular autoload situation)."
  (let ((files (*files-being-loaded*)))
    (any (lambda (path)
           (or
            ;; Check if path ends with /file.el
            (string-suffix? (string-append "/" autoload-file ".el") path)
            ;; Check if path ends with /file (no extension)
            (string-suffix? (string-append "/" autoload-file) path)
            ;; Check exact match
            (equal? autoload-file path)
            ;; Check if path is just file.el (no directory)
            (equal? (string-append autoload-file ".el") path)))
         files)))

(define (elisp-autoload-do-load fundef funname macro-only)
  "Scheme implementation of autoload-do-load.
Load FUNDEF which should be an autoload.
If non-nil, FUNNAME should be the symbol whose function value is FUNDEF,
in which case the function returns the new autoloaded function value.
If equal to 'macro, MACRO-ONLY specifies that FUNDEF should only be loaded if
it defines a macro."
  ;; Check if fundef is an autoload form (autoload FILE ...)
  (if (not (and (pair? fundef) (eq? (car fundef) (elisp-intern "autoload" #nil))))
      fundef
      (let* ((kind ((symbol-function 'nth) 4 fundef))
             (qt ((symbol-function 'symbol-value) (elisp-intern "t" #nil)))
             (qmacro (elisp-intern "macro" #nil)))
        ;; If macro-only is 'macro and kind isn't t or 'macro, return fundef unchanged
        (if (and (eq? macro-only qmacro)
                 (not (or (eq? kind qt) (eq? kind qmacro))))
            fundef
            (let* ((autoload-file ((symbol-function 'car) ((symbol-function 'cdr) fundef)))
                   ;; ignore-errors is true if macro-only is set but kind isn't macro/t
                   (ignore-errors (if (or (eq? kind qt) (eq? kind qmacro))
                                      #nil
                                      macro-only)))
              ;; Check for circular autoload BEFORE loading
              ;; If circular, return fundef unchanged - callers will handle gracefully
              (if (and (string? autoload-file)
                       (file-being-loaded? autoload-file))
                  ;; Circular autoload - return unchanged, function will be defined later
                  fundef
                  ;; Normal case - proceed to load the file
                  (begin
                    ((symbol-function 'load) autoload-file ignore-errors qt #nil qt)
                    ;; Check result
                    (cond
                     ;; If funname is nil or ignore-errors is set, return nil
                     ((or (eq? funname #nil) (not (eq? ignore-errors #nil)))
                      #nil)
                     (else
                      (let ((fun ((symbol-function 'indirect-function) funname #nil)))
                        (if (not ((symbol-function 'equal) fun fundef))
                            ;; Function was defined, return it
                            fun
                            ;; Function still equals autoload form - check for circular load
                            (if (and (string? autoload-file)
                                     (file-being-loaded? autoload-file))
                                ;; Circular autoload - return fundef unchanged
                                fundef
                                ;; Real error - function wasn't defined
                                ((symbol-function 'error)
                                 "Autoloading file %s failed to define function %s"
                                 (let ((hist ((symbol-function 'symbol-value)
                                              (elisp-intern "load-history" #nil))))
                                   (if (pair? hist)
                                       ((symbol-function 'car) ((symbol-function 'car) hist))
                                       ""))
                                 ((symbol-function 'symbol-name) funname))))))))))))))

;;;
;;; Compound Operations
;;;

(define (elisp-setup-load-environment found loads-in-progress file purify-flag is-native-elisp)
  "Compound function: Set up load environment including recursive loads, bindings, and filenames.
This consolidates recursive load detection, loads-in-progress management, lexical binding setup,
effective filename computation, and history file name computation.
Returns: (new-loads-in-progress . (lexical-binding . (found-eff . hist-file-name)))"
  (elisp-count-recursive-loads found loads-in-progress)
  (let ((new-loads-in-progress (elisp-handle-loads-in-progress found loads-in-progress)))
    (let ((lexical-binding (elisp-handle-lexical-binding-specbind)))
      (let ((found-eff (elisp-compute-effective-filename found is-native-elisp)))
        (let ((hist-file-name (elisp-compute-hist-file-name file found-eff purify-flag)))
          (cons new-loads-in-progress
                (cons lexical-binding
                      (cons found-eff hist-file-name))))))))

(define (elisp-detect-lexical-binding port)
  "Detect lexical binding from first line of file.
  Returns #t for lexical binding, #f for dynamic binding, 'none for no cookie.
  This replicates the logic from lisp_file_lexical_cookie_scm_port."

  (define (skip-whitespace)
    "Skip whitespace characters"
    (let ((ch (peek-char port)))
      (when (and (not (eof-object? ch)) (char-whitespace? ch))
        (read-char port)
        (skip-whitespace))))

  (define (read-first-line)
    "Read first line as string"
    (let loop ((chars '()))
      (let ((ch (peek-char port)))
        (cond
         ((or (eof-object? ch) (char=? ch #\newline))
          (list->string (reverse chars)))
         (else
          (read-char port)
          (loop (cons ch chars)))))))

  ;; Check if first character indicates a comment or shebang
  (let ((first-ch (peek-char port)))
    (cond
     ((eof-object? first-ch) 'none)
     ((char=? first-ch #\;)
      ;; Comment line - read and parse for lexical-binding
      (let ((line (read-first-line)))
        (cond
         ((string-contains line "lexical-binding: t") #t)
         ((string-contains line "lexical-binding: nil") #f)
         (else 'none))))
     ((and (char=? first-ch #\#)
           (not (eof-object? (peek-char port))))
      ;; Potential shebang line
      (read-char port) ; consume #
      (let ((second-ch (peek-char port)))
        (if (char=? second-ch #\!)
            (begin
              ;; Read shebang line and parse for lexical-binding
              (let ((line (read-first-line)))
                (cond
                 ((string-contains line "lexical-binding: t") #t)
                 ((string-contains line "lexical-binding: nil") #f)
                 (else 'none))))
            (begin
              ;; Not a shebang, push back the #
              (unread-char #\# port)
              'none))))
     (else 'none))))

(define (elisp-setup-port-input is-module is-native-elisp fd-valid)
  "Set up input port based on file type.
  This replicates the conditional setup from Fload lines 1108-1128.
  Returns: 'close-fd, 'setup-port, or 'continue."

  (cond
   ((or is-module is-native-elisp)
    ;; Module/native elisp - close file descriptor
    (if fd-valid 'close-fd 'continue))
   (else
    ;; Regular elisp - set up port
    'setup-port)))

;; Bridge function that reuses existing Fload Scheme migrations

(define (search-elisp-load-path file)
  "Search for FILE in Elisp load-path.
Returns the full path to the file if found, #f otherwise.
Only returns actual files, not directories."
  (let ((load-path ((symbol-function 'symbol-value) 'load-path)))
    (let loop ((paths load-path))
      (cond
        ((eq? paths #nil) #f)  ; end of list
        (else
         (let* ((dir ((symbol-function 'car) paths))
                (full-path ((symbol-function 'expand-file-name) file dir)))
           (if (and (file-exists? full-path)
                    (not ((symbol-function 'file-directory-p) full-path)))
               full-path
               (loop ((symbol-function 'cdr) paths)))))))))

(define* (elisp-load file #:optional (noerror #nil) (nomessage #nil) (nosuffix #nil) (must-suffix #nil))
  "Bridge function that handles full Fload protocol using Guile elisp compilation.
Optional args default to nil, matching Elisp's (load FILE &optional NOERROR NOMESSAGE NOSUFFIX MUST-SUFFIX)."
  (catch #t
    (lambda ()
      (format (current-error-port) "loading ~a~%" file)
      ;; File validation and handler check (reuse existing)
      (let ((handler-result (elisp-validate-and-check-handler file noerror nomessage nosuffix must-suffix)))
        (when handler-result
          (throw 'early-return handler-result)))

      ;; File path processing and suffix determination (reuse existing)
      (let* ((path-result (elisp-process-load-file-path file nosuffix must-suffix))
             (processed-file (car path-result))
             (suffixes (cdr path-result)))
        ;; Find file using Elisp load-path search
        (let ((found (or
                      ;; Search Elisp load-path (not Guile's %load-path)
                      (search-elisp-load-path processed-file)
                      (search-elisp-load-path (string-append processed-file ".el"))
                      ;; Also try current directory if not found in load-path
                      (and (file-exists? processed-file) processed-file)
                      ;; Try with .el suffix in current directory
                      (and (file-exists? (string-append processed-file ".el"))
                           (string-append processed-file ".el")))))
          (unless found
            (if noerror
                (throw 'early-return #f)
                (error "Cannot open load file" file)))

          ;; FIX-20260114-guilemacs: Check for recursive load cycle
          ;; If this file is already being loaded (circular require), skip re-loading
          ;; This allows circular requires like gnus-sum <-> gnus-art to work
          (let ((load-count (count (lambda (f) (equal? f found)) (*files-being-loaded*))))
            (when (> load-count 0)
              ;; File is already being loaded - skip to prevent infinite loop
              ;; Also early-provide the feature so require doesn't error
              (format (current-error-port) "skipping circular load of ~a (already loading)~%" found)
              (let* ((base (basename found))
                     (feature-name (if (string-suffix? ".el" base)
                                      (substring base 0 (- (string-length base) 3))
                                      base))
                     (feature-sym (string->symbol feature-name)))
                (elisp-provide feature-sym))
              (throw 'early-return #t))

            ;; Step 4: Setup load environment (reuse existing)
            (let ((setup-env-func (resolve-ref "emacs loader"
                                               "elisp-setup-load-environment")))
              (when setup-env-func
                (setup-env-func found '() file #f #t))) ; simplified params

            ;; Step 5: Use enhanced elisp compilation instead of C reading
            ;; Wrap in parameterize to track this file as being loaded
            (parameterize ((*files-being-loaded* (cons found (*files-being-loaded*))))
              (load-elisp-full found noerror nomessage nosuffix must-suffix))))))

    (lambda (key . args)
      (cond
        ((eq? key 'early-return) (car args))
        (noerror #f)
        (else (apply throw key args))))))

(define (resolve-ref module-name symbol-name)
  (catch #t
    (lambda ()
      (let ((mod (resolve-module (string->symbol module-name))))
        (and mod (module-ref mod (string->symbol symbol-name)))))
    (lambda (key . args) #f)))

(define (elisp-validate-and-check-handler file noerror nomessage nosuffix must-suffix)
  "Compound function: Validate file and check for magic file name handlers.
This consolidates elisp-validate-load-file and elisp-check-file-handler.
Returns: handler result if handler found, #f if should continue with normal loading."
  (elisp-validate-load-file file)
  (elisp-check-file-handler file noerror nomessage nosuffix must-suffix))

(define (elisp-check-file-handler file noerror nomessage nosuffix must-suffix)
  "Check for magic file name handler and call it if found.
  This replicates the handler check from Fload lines 973-977.
  Returns handler result or #f if no handler."
  ;; FIX-20261011-guilemacs: the Emacs C bootstrap installs
  ;; find-file-name-handler.  In a plain `guile' process the cell is
  ;; empty, so the apply `((symbol-function 'find-file-name-handler) ...)'
  ;; raised `wrong-type-arg "Wrong type to apply: #nil"' FIRST, inside the
  ;; `let' binding -- before the `(if handler ...)' test ever ran.  (Guile
  ;; treats `#nil' as FALSEY at the Scheme `if': `(if #nil ...)' takes the
  ;; else branch.  The C `scm_is_true' accepts `#nil', but the loader uses
  ;; the Scheme `if', not the C function.)  Guard the call with the Scheme
  ;; predicate `symbol-fbound?' and test the Elisp nil explicitly: an
  ;; empty cell means "no handler", so take the no-handler branch.
  (if (not (symbol-fbound? 'find-file-name-handler))
      #f
      (let ((handler ((symbol-function 'find-file-name-handler) file 'load)))
        (if (not (eq? handler #nil))
            ;; Call the handler with all arguments
            ((symbol-function 'funcall) handler 'load file noerror nomessage nosuffix must-suffix)
            ; No handler found
            #f))))


(define (fresh-go? go src)
  (and go
       (file-exists? go)
       (>= (stat:mtime (stat go)) (stat:mtime (stat src)))))

(define (load-elisp file)
  ;; M55 imp-4 (cr.org M2): load-elisp is an exported entry point, so it can
  ;; be reached in a plain `guile' process too.  Test the elisp compiler
  ;; FIRST (the narrow catch) and take the source-reading branch when it is
  ;; absent, like load-elisp-full.  `compiled-file-name' and `compile-file'
  ;; are Guile-compiler cells and are UNBOUND in a plain `guile' process
  ;; (measured), so compute the .go path ONLY on the compiler branch.  Row
  ;; 10 stays C for the full-Emacs path.
  (let ((src (%search-load-path file)) ; find foo.el on %load-path
        (el  (elisp-loader-compiler-available?)))
    (unless src
      (error "Not found on %load-path" file))
    (if el
        (let ((go (compiled-file-name src))) ; cache path for .go
          (if (fresh-go? go src)
              (load-compiled go)
              (begin
                (compile-file src
                              #:from el ; 'elisp
                              ;#:to 'value ; warmbyte , FIX-GUILE: cant combine with output-file
                              #:output-file go)
                (load-compiled go))))
        ;; M55 imp-4: no elisp compiler, READ and RUN the source.
        (elisp-load-source-file src))))

;; Enhanced version that handles full Fload parameters
(define (load-elisp-full found-file noerror nomessage nosuffix must-suffix)
  "Load elisp file with compilation on the full-Emacs path, or by
reading the source when the elisp compiler is absent (M55 imp-4)."
  (catch #t
    (lambda ()
      (let* ((src found-file)
             (go (string-append src ".go")) ; FIX: compiled-file-name returns #f ?!
             ;; Load our custom elisp language to override system elisp.
             ;; When the C compiler is absent this is #f (imp-4): take the
             ;; source-reading branch instead.  Row 10 stays C otherwise.
             (el (elisp-loader-compiler-available?))
             ;; Save current load-file-name for restoration
             (old-load-file-name ((symbol-function 'symbol-value) 'load-file-name)))
        ;; Bind load-file-name to current file during loading
        (dynamic-wind
          (lambda ()
            (set-symbol-value! 'load-file-name found-file))
          (lambda ()
            (cond
             (el
              (if (fresh-go? go src)
                  (load-compiled go)
                  (begin
                    (compile-file src
                                  #:from el
                                  #:output-file go)
                    (load-compiled go))))
             (else
              ;; M55 imp-4: no elisp compiler, READ and RUN the source.
              (elisp-load-source-file src)))
            #t) ; return t on success
          (lambda ()
            (set-symbol-value! 'load-file-name old-load-file-name)))))
    (lambda (key . args)
      (if noerror
          #f ; return nil on error if noerror is true
          (apply throw key args)))))

;;;
;;; M60 imp-5 -- row 20: `require', the C DEFUN of src/fns.c :3496
;;;
;;; The cell follows `Frequire' step by step: CHECK_SYMBOL, a `memq'
;;; against `features', the elisp `load' protocol, the second `memq', and
;;; the "Required feature" error.
;;;
;;; It calls `elisp-load' (:725), NOT `load-elisp' (:831).  Frequire calls
;;; the elisp `load' protocol (:3582 `load_with_autoload_queue'), and
;;; `elisp-load' owns that protocol: it searches the elisp `load-path'
;;; VARIABLE and skips a file that is already being loaded.
;;
;; FIX-20261021-guilemacs: standalone-load cell.  A full Emacs keeps the
;; C DEFUN, so `init-loader' installs this cell only when the function
;; cell is EMPTY (see the guarded block of `init-loader').
;;
;; NOT ported (C state, named as limits in the commit message):
;; `features_being_loaded' (src/fns.c :3488), `require_nesting_list'
;; (:3481), `subfeatures', `Vcurrent_load_list', the `after-load-alist'
;; hook, and the 2nd error message (:3606).
(define* (elisp-require feature #:optional (filename #nil) (noerror #nil))
  "If FEATURE is not loaded, load it from FILENAME, then return FEATURE.
FILENAME defaults to the print name of FEATURE.  NOERROR returns the
elisp nil instead of a `load' error."
  ;; CHECK_SYMBOL (src/fns.c :3521).
  (unless (symbol? feature)
    (scm-error 'wrong-type-arg "require" "Wrong type argument: ~S"
               (list feature) #f))
  ;; Fmemq against `features'.  `features' is bound by the row-19 form of
  ;; `init-loader' (:1238), before this cell is reachable, so no bind is
  ;; needed here.  A loaded feature does NOT load the file again.
  (if (memq feature (symbol-value 'features))
      feature
      (let* (;; NILP: both the elisp nil (#nil) and Scheme #f count as
             ;; "no FILENAME", so the name comes from the feature symbol.
             (from-feature? (not (elisp-loader-truthy? filename)))
             (name (if from-feature? (symbol->string feature) filename))
             ;; `load_with_autoload_queue' (:3582): NOMESSAGE is t,
             ;; NOSUFFIX is nil, MUST-SUFFIX is t only when the name comes
             ;; from the feature symbol.
             (result (elisp-load name noerror #t #nil from-feature?)))
        ;; NILP of the load value.  The NOERROR path of `elisp-load'
        ;; returns Scheme #f (:785), and `(eq? #f #nil)' is false, so a
        ;; plain nil test would read a FAILED load as a success.
        (if (not (elisp-loader-truthy? result))
            #nil
            (if (memq feature (symbol-value 'features))
                feature
                ;; The C message names SYMBOL_NAME (feature), not FILENAME
                ;; (src/fns.c :3604).
                (error "Required feature `~a' was not provided"
                       (symbol->string feature)))))))

;;;
;;; M55 imp-2 -- the reachable runtime cells in Scheme
;;;
;;; The loader applies 7 runtime function cells on the real plain-guile
;;; load path (docs/m55-plan.org section 3.2, rows 3 ... 9).  In a plain
;;; `guile' process the C bootstrap is absent, so every cell is empty.
;;; imp-2 installs them, in call order, with no C fallback.  Two cells
;;; need a small Scheme mechanism: `expand-file-name' (a path join) and
;;; `file-directory-p' (a stat).  The other 5 reuse existing pure-Scheme
;;; procedures: elisp-get-load-suffixes, elisp-append, symbol-value,
;;; elisp-car, elisp-cdr.

;; `expand-file-name' for the loader load-path search.  The loader calls
;; it with the file name and a load-path directory, where FILE is the
;; (possibly relative) name and DIR is a load-path entry.  Only the
;; load-path case is handled: an absolute FILE returns as-is; else join
;; DIR and FILE with one "/".  A #nil or empty DIR returns FILE (the
;; elisp-normalize-load-path call site passes #nil).
(define (elisp-loader-expand-file-name file dir)
  (cond
    ((or (eq? dir #nil) (not (string? dir)) (string-null? dir)) file)
    ((not (string? file)) file)
    ((string-prefix? "/" file) file)
    (else (string-append (if (string-suffix? "/" dir) dir (string-append dir "/"))
                         file))))

;; `file-directory-p' from the Scheme stat.  The (emacs fileio) cell is
;; C-backed and is NOT reusable (brief.org section 10).  A stat error
;; (a missing path) folds to #f, like the C predicate.
(define (elisp-loader-file-directory-p path)
  (catch #t
    (lambda () (eq? 'directory (stat:type (stat path))))
    (lambda args #f)))

;; `file-name-directory' for the elisp `load' protocol.
;;
;; M60 imp-5, MEASURED: `elisp-process-load-file-path' (:246 ... :260)
;; applies `string-suffix-p' and `file-name-directory' on every MUST-SUFFIX
;; call, and both cells are EMPTY in a plain `guile' process.  A full Emacs
;; owns the 2 C DEFUNs; `(emacs fileio)' is C-backed and is NOT reusable
;; (brief.org section 10), so the loader holds a small Scheme path split.
;; The Emacs contract: the directory part WITH the trailing "/"; a name
;; with no directory part returns #nil.
(define (elisp-loader-file-name-directory file)
  (if (or (not (string? file)) (string-null? file))
      #nil
      (let loop ((i (- (string-length file) 1)))
        (cond
         ((< i 0) #nil)
         ((char=? (string-ref file i) #\/) (substring file 0 (+ i 1)))
         (else (loop (- i 1)))))))

;;;
;;; M55 imp-4 -- the source-reading load path (C delta 0)
;;;
;;; Load an .el file when the elisp compiler is absent, by READING the
;;; source text and evaluating it.  The C elisp compiler (row 10,
;;; lookup-language 'emacs-elisp) STAYS in place for the full-Emacs path.
;;; imp-4 only adds a branch that runs when that lookup raises; on the
;;; source-reading branch no compile-file and no eval-elisp (row 10) runs.
;;;
;;; FIX-20261015-guilemacs: the reader applies 3 function cells that the
;;; C bootstrap owns in a full Emacs (intern, concat, substring), and the
;;; read-eval loop applies the eval cell.  In a plain `guile' process
;;; they are EMPTY, so the reader can not even read a form (measured:
;;; wrong-type-arg "Wrong type to apply: #nil").  The loader POLICY
;;; installs small pure-Scheme procedures for them, in call order, with a
;;; symbol-fbound? guard so a present C cell is KEPT.  No C fallback.

;; `intern' reuses the pure-Scheme elisp-intern (emacs utils).

;; `concat' joins STRING arguments only; `substring' cuts a string with
;; an optional end.  Both tolerate the #nil forms the reader may pass.
;;
;; F7 (cr.org section 4): these are READER SHIMS, NOT the Emacs
;; procedures.  The Emacs `concat' also accepts a list, a vector, or an
;; integer char, and a non-string argument folds to its printed form
;; here.  The reader calls `concat' 2 times and `substring' 1 time, so
;; the load path is safe.  Do not expose these as the Emacs definitions.
(define (elisp-loader-concat . sequences)
  (apply string-append
         (map (lambda (seq)
                (cond
                 ((string? seq) seq)
                 ((eq? seq #nil) "")
                 ((null? seq) "")
                 (else (format #f "~a" seq))))
              sequences)))

(define (elisp-loader-substring string start . rest)
  (let* ((len (string-length string))
         (from (if (or (eq? start #nil) (not (integer? start))) 0 start))
         (end (if (null? rest)
                  len
                  (let ((e (car rest)))
                    (if (or (eq? e #nil) (not (integer? e))) len e)))))
    (substring string from end)))

;; The eval cell.  A minimal Scheme elisp evaluator over the reader datum
;; (brief.org section 7 default scope).  Special forms: quote, setq, if,
;; progn, let, lambda, and function application.  This is NOT the elisp
;; compiler (row 10): it never calls lookup-language or compile.
(define (elisp-loader-truthy? obj)
  (and (not (eq? obj #nil)) (not (eq? obj #f))))

(define (elisp-loader-eval-seq forms)
  (let ((result #nil))
    (for-each (lambda (form) (set! result (elisp-loader-eval form))) forms)
    result))

;; F3 (cr.org section 4): an unbound FUNCTION raises `void-function',
;; like elisp.  Without this the evaluator applied #nil and returned
;; #nil with no error, so a broken file looked like a clean load.
;;
;; M60 imp-14 -- row 34: a function cell may hold a SYMBOL, and a CALL
;; follows the chain to the procedure.  C peer is `indirect_function'
;; (src/data.c :2209, used by `Ffuncall'): C resolves the cell at CALL
;; time, not at `defalias' time, so `(symbol-function 'a)' stays the
;; SYMBOL that `defalias' wrote.  The resolver below is the same order:
;; cell first, apply second.
;; The 100-link count is a guilemacs SAFETY, not a C port: C has no
;; count here and a ring loops forever.  The raise names the symbol that
;; the CALLER used, so a ring A -> B -> A reports `a', not `b'.
;; FIX-20261022-guilemacs: the check is a link count, not a visited set.
(define %elisp-loader-indirect-limit 100)

(define (elisp-loader-resolve-function fn)
  "Return the procedure that FN names, or #f when FN names no procedure.
FN is a procedure, a symbol with a function cell, or a chain of symbols.
A chain longer than `%elisp-loader-indirect-limit' raises
`cyclic-function-indirection' with FN, the symbol of the call."
  (let loop ((value fn) (links 0))
    (cond
      ((procedure? value) value)
      ((symbol? value)
       (if (>= links %elisp-loader-indirect-limit)
           (throw 'cyclic-function-indirection fn)
           (loop (symbol-function value) (+ links 1))))
      (else #f))))

(define (elisp-loader-apply fn args)
  ;; FN is the HEAD symbol of the call, or a procedure.  The CALLER name
  ;; is passed through, so `void-function' and
  ;; `cyclic-function-indirection' report it, not the last link.
  (let ((proc (elisp-loader-resolve-function fn)))
    (if proc
        (apply proc args)
        (throw 'void-function fn))))

(define (elisp-loader-eval form)
  (cond
    ((symbol? form)
     (if (symbol-bound? form)
         (symbol-value form)
         ;; F3: an unbound VARIABLE raises `void-variable', like elisp.
         (throw 'void-variable form)))
    ((pair? form) (elisp-loader-eval-form form))
    (else form)))

;; F4 (cr.org section 4): elisp `let' and a lambda argument bind
;; dynamically and RESTORE the previous value on exit.  Bind through this
;; thunk factory, then call every restore thunk after the body, so a
;; loaded file can not corrupt global state.
(define (elisp-loader-bind-thunk name value)
  (if (symbol-bound? name)
      (let ((old (symbol-value name)))
        (set-symbol-value! name value)
        (lambda () (set-symbol-value! name old)))
      (begin
        (set-symbol-value! name value)
        ;; FIX-20261015-guilemacs: the elisp value slot has no Scheme
        ;; "unbind".  A previously-unbound name restores to elisp nil; a
        ;; bound name (the common case) restores exactly.
        (lambda () (set-symbol-value! name #nil)))))

;; M60 imp-19 -- L4 is CLOSED for 3 parameter shapes.  The walk has 4
;; branches.  C peer: `funcall_lambda' (src/eval.c :2167).  C tests the 2
;; MARKER symbols on the parameter list BEFORE it binds a cell
;; (`Qand_rest' :2200, `Qand_optional' :2207) and builds the rest
;; argument with `Flist' (:2218).  B1 a non-pair tail ENDS the walk: that
;; is the empty parameter list, a short argument list and a bare `args'
;; (L45, L46).  B2 `&optional' writes NO cell; the name after it binds
;; the elisp nil `#nil' when no argument is left (D1, D2).  B3 `&rest'
;; binds the WHOLE remaining Scheme list and ENDS the walk (D3, D4); a
;; bare `&rest' binds nothing.  B4 a plain name takes the next positional
;; argument.  The walk tests `pair?' before EVERY `(cdr as)', so it can
;; NOT call `(cdr args)' past the end of a short list: that raise was the
;; L4 wall.
(define (elisp-loader-bind-params! params args)
  "Bind PARAMS to ARGS.  Return the list of restore thunks."
  (let loop ((ps params) (as args) (restore '()))
    (cond
      ;; B1: empty parameter list, or a non-list tail: nothing to bind.
      ((not (pair? ps)) restore)
      ;; B2: `&optional' marks the names that follow.  No cell (D2).
      ((eq? (car ps) '&optional) (loop (cdr ps) as restore))
      ;; B3: `&rest' marks 1 name.  It binds the remaining list and ends
      ;; the walk (D3, D4).  A bare `&rest' binds nothing.
      ((eq? (car ps) '&rest)
       (if (pair? (cdr ps))
           (cons (elisp-loader-bind-thunk (cadr ps) as) restore)
           restore))
      ;; B4: a required OR optional name: positional, or elisp nil (D1).
      (else
       (let ((value (if (pair? as) (car as) #nil)))
         (loop (cdr ps)
               (if (pair? as) (cdr as) '())
               (cons (elisp-loader-bind-thunk (car ps) value) restore)))))))

;; M60 imp-9 fix (cr.org F5): elisp accepts a BARE SYMBOL binding, as in
;; `(let (q) ...)'.  It binds elisp nil, the same as `((q))'.  The old
;; path took `(car binding)' of a SYMBOL and raised `wrong-type-arg'.
(define (elisp-loader-binding-name binding)
  (if (symbol? binding) binding (car binding)))

(define (elisp-loader-binding-init binding)
  (if (and (pair? binding) (pair? (cdr binding)))
      (elisp-loader-eval (cadr binding))
      #nil))

(define (elisp-loader-make-procedure params body)
  (lambda args
    (let ((restore (elisp-loader-bind-params! params args)))
      (dynamic-wind
        (lambda () #t)
        (lambda () (elisp-loader-eval-seq body))
        (lambda () (for-each (lambda (thunk) (thunk)) restore))))))

;; M60 imp-7 -- row 23: the macro store of (emacs loader).  An alist maps
;; the elisp NAME to its EXPANDER procedure.  The elisp FUNCTION cell is
;; NOT touched: the `symbol-function' reader and the `fbound?' predicate
;; read that cell, and a full Emacs owns it in C.
;; L9: the table is process-GLOBAL and has no reset, so a 2nd `load'
;; keeps the old expanders.  This is a limit, not a claim.
(define elisp-loader-macro-table '())

(define (elisp-loader-macro-ref name)
  (let ((hit (assq name elisp-loader-macro-table)))
    (if hit (cdr hit) #f)))

;; M60 imp-7 fix -- L8 (cr.org F3): a `defun' SHADOWS a macro of the same
;; name.  Emacs keeps the 2 forms in ONE cell, so the later `defun' wins.
;; Here the cells are separate, so the table entry must be DROPPED.
(define (elisp-loader-macro-drop! name)
  (set! elisp-loader-macro-table
        (remove (lambda (entry) (eq? (car entry) name))
                elisp-loader-macro-table)))

;; M60 imp-21 -- row 28b: the backquote VALUE BUILDER.
;; The read loop interns the NAME only, so the head that a real file
;; reaches is the 1-CHARACTER symbol: `elisp-parse-backquote-with-list-
;; construction' (reader.scm :540) conses `(intern "`")' at :545, and the
;; read loop calls it at :1568.  `(eq? (string->symbol "`") 'backquote)'
;; is #f (measured).  The 2 unquote PRODUCERS agree: `,@' at
;; reader.scm :560/:1689 and `,' at :567/:1692 use `elisp-intern', which
;; is `string->symbol' (utils.scm :106).
;; The C peer interns the NAME only too: `DEFSYM (Qbackquote, "`")' at
;; src/lread.c :3500, and src/eval.c holds 0 `backquote' match.  The walk
;; below is therefore a DECISION, not a port.
(define elisp-loader-backquote-head (string->symbol "`"))
(define elisp-loader-unquote-head (string->symbol ","))
(define elisp-loader-unquote-spliced-head (string->symbol ",@"))

;; LIMITS of this row.  These are NAMED limits, never claims:
;; L53 the unquoted names resolve on the DYNAMIC binding model of this
;;    evaluator (L3).  Emacs uses the lexical model.
;; L54 `,@' of a value that is not a proper list raises a Guile
;;    `misc-error'.  This loader has no elisp `signal' path (L20 / L21),
;;    so the error text names no elisp symbol.
;; L55 the depth rule is LOCAL to this walk: an unquote at a depth higher
;;    than 1 keeps the structure and does NOT evaluate.  C `Fread' has no
;;    depth, so the rule is a DECISION.
;; L56 a `,@' at depth 1 in a VALUE context RAISES.  This port raises; a
;;    full Emacs does NOT.  The splice branch of `backquote-process'
;;    (lisp/emacs-lisp/backquote.el :166) answers the tag 2 with the form
;;    `x' (:171), and the `backquote' macro DROPS the tag
;;    (`(cdr (backquote-process structure))', :110), so `,@x' expands to
;;    `x'.  The raise is a DECISION of this port, not a port of C.  A
;;    deeper `,@' keeps the structure, as L55 does.
;; L57 a DOTTED unquote tail differs: the reader turns `(1 . ,x)' into
;;    (backquote (1 (, x))), so the walk returns (1 , x) and NOT (1 . 5).
;;    The cause is the reader tail read, and this imp changes no reader.
;; L58 an unquote with MORE than 1 argument does NOT raise: `(, a b)' at
;;    depth 1 evaluates `a' and DROPS `b', because the walk reads
;;    `(cadr form)' only.  A full Emacs raises "Multiple args to , are
;;    not supported" (:162), and the same for `,@' (:170).  This row
;;    needs no shape, so the limit is named and no code is changed.
;; The SHAPE of a DELAYED unquote is a proper 2-element list
;; `(<,> form)': `backquote-delay-process' (:121) listifies the `,' head
;; against the processed CDR, and the cdr of a `,x' form is the LIST
;; (x), so the `,' lands in the head of a pair whose tail is a list.  A
;; dotted pair can not come out.  The argument stays the FORM and is not
;; evaluated (cr.org F6 of the imp-21 round: the DOTTED claim is refuted
;; by the source, not by a run; vanilla Emacs does not run on this host).
;; The value is a FRESH SCHEME list or a FRESH SCHEME vector.  It is not a
;; byte-code constant, and no `list' / `vector' cell is touched: this walk
;; is 1 pass and there is no compile phase in this loader.
;; The reader has 2 live backquote producers, and
;; `elisp-parse-backquote-from-port' (reader.scm :528) is a 3rd, dead one
;; (0 caller).  This walk accepts BOTH live heads, so the readers agree
;; again.  The producers stay 2; their merge is the next candidate.

;; Walk 1 FORM at 1 DEPTH.  An atom returns ITSELF.  Every returned level
;; is a FRESH pair: the loader KEEPS the form that it evaluates, and a
;; macro expander can run 2 times, so a sub-list that shares a pair with
;; the input can be mutated by a later caller.
(define (elisp-loader-backquote-walk form depth)
  "Return the value of backquote FORM at DEPTH.  Every level is fresh."
  (cond
    ;; A VECTOR is a value context too, so a `,' or `,@' inside it must be
    ;; walked: an untouched vector answers a WRONG value with no raise
    ;; (cr.org F3 of the imp-21 round).
    ((vector? form) (elisp-loader-backquote-walk-vector form depth))
    ((not (pair? form)) form)
    (else
     (let ((head (car form)))
       (cond
         ;; L55: depth 1 evaluates; a deeper level keeps the structure.
         ;; A DELAYED unquote answers the proper 2-element list
         ;; `(<,> form)' and the form is NOT evaluated (see L56 ... L58
         ;; above): `backquote-delay-process' listifies the `,' head
         ;; against the processed CDR.
         ((eq? head elisp-loader-unquote-head)
          (if (= depth 1)
              (elisp-loader-eval (cadr form))
              (cons elisp-loader-unquote-head
                    (cons (elisp-loader-backquote-walk (cadr form) (- depth 1))
                          #nil))))
         ;; L56: a splice at depth 1 is legal in a LIST context only.
         ;; `walk-list' owns that case, so this is a VALUE context.  A
         ;; deeper splice keeps the structure, as L55 does (cr.org F2).
         ((eq? head elisp-loader-unquote-spliced-head)
          (if (= depth 1)
              (error "backquote: `,@' is legal inside a list only" form)
              (cons elisp-loader-unquote-spliced-head
                    (cons (elisp-loader-backquote-walk (cadr form) (- depth 1))
                          #nil))))
         ;; The nested case: keep the head that the producer made.
         ((or (eq? head elisp-loader-backquote-head) (eq? head 'backquote))
          (cons head
                (cons (elisp-loader-backquote-walk (cadr form) (+ depth 1))
                      #nil)))
         (else (elisp-loader-backquote-walk-list form depth)))))))

;; Walk 1 LIST at 1 DEPTH and build a FRESH list.  A splice is tested on
;; the ELEMENT shape here, so the data carries no sentinel object.
(define (elisp-loader-backquote-walk-list form depth)
  "Return a fresh list for backquote list FORM at DEPTH.  A `,@' at DEPTH
1 appends the ELEMENTS of its value; a non-pair tail is walked and kept."
  (let loop ((rest form))
    (cond
      ;; The normal list end needs no test: `(null? #nil)' is #t and
      ;; `(pair? #nil)' is #f, so a dotted tail is WALKED here.
      ((not (pair? rest)) (elisp-loader-backquote-walk rest depth))
      ((and (= depth 1)
            (pair? (car rest))
            (eq? (car (car rest)) elisp-loader-unquote-spliced-head))
       (let ((value (elisp-loader-eval (cadr (car rest)))))
         (if (list? value)
             (append value (loop (cdr rest)))
             (error "backquote: `,@' needs a proper list" value))))
      (else
       (cons (elisp-loader-backquote-walk (car rest) depth)
             (loop (cdr rest)))))))

;; Walk 1 VECTOR at 1 DEPTH and build a FRESH vector.  Emacs expands a
;; vector to (vector ...) with the same element rules: the `vectorp'
;; branch of `backquote-process' (lisp/emacs-lisp/backquote.el :138)
;; processes `(append s ())' and rebuilds a `vector' / `vconcat' call, so
;; `[1 ,(+ 1 1)]' gives [1 2] and `[1 ,@(list 1 2)]' gives [1 1 2] by
;; SOURCE (vanilla Emacs does not run on this host: no dump file).  The
;; ELEMENTS go through `walk-list' and a depth-1 `,@' spreads there.
;; Before this, the walk returned a vector UNCHANGED, so its unquotes
;; were a WRONG value with no raise.
(define (elisp-loader-backquote-walk-vector vec depth)
  "Return a fresh vector for backquote VECTOR VEC at DEPTH."
  (list->vector
   (elisp-loader-backquote-walk-list (vector->list vec) depth)))

(define (elisp-loader-eval-form form)
  (let ((head (car form)))
    (cond
      ((not (symbol? head))
       (elisp-loader-apply (elisp-loader-eval head)
                           (map elisp-loader-eval (cdr form))))
      ((eq? head 'quote) (cadr form))
      ;; M60 imp-21 -- row 28b: the backquote builder.  It is placed
      ;; BEFORE the `function' branch and BEFORE the macro-table test:
      ;; the argument of a backquote is UNEVALLED, and the branch tests
      ;; NO cell.  Both heads are tested, so the 2 live reader producers
      ;; agree again.
      ((or (eq? head elisp-loader-backquote-head) (eq? head 'backquote))
       (elisp-loader-backquote-walk (cadr form) 1))
      ;; M60 imp-14 -- row 34: `function' is a SPECIAL FORM (unevalled).
      ;; It returns a SYMBOL argument as it is, so the cell of
      ;; (defalias 'string= #'string-equal) holds the SYMBOL
      ;; `string-equal'.  A function cell can NOT do this: the evaluator
      ;; evaluates the arguments of a call first, so an installed
      ;; `function' procedure would raise `void-variable string-equal'.
      ;; C has no DEFUN ("function") in src/ (measured): only the NAME
      ;; is interned (src/lread.c :3519) and the reader builds the list
      ;; for `#'x' (reader.scm :831).  The reader needs no change.
      ;; L35: a non-symbol ARG is EVALUATED, so `#'(lambda ...)' gives
      ;; the procedure, not the raw form.  1 limit stays: a `(closure
      ;; ...)' literal is not a value that this reader builds.
      ((eq? head 'function)
       (let ((arg (cadr form)))
         (if (symbol? arg) arg (elisp-loader-eval arg))))
      ((eq? head 'setq)
       (let loop ((rest (cdr form)))
         (cond
          ((null? rest) #nil)
          ((null? (cdr rest)) (elisp-loader-eval (car rest)))
          (else
           (set-symbol-value! (car rest) (elisp-loader-eval (cadr rest)))
           (loop (cddr rest))))))
      ((eq? head 'if)
       (if (elisp-loader-truthy? (elisp-loader-eval (cadr form)))
           (elisp-loader-eval (caddr form))
           (if (pair? (cdddr form)) (elisp-loader-eval (cadddr form)) #nil)))
      ((eq? head 'progn) (elisp-loader-eval-seq (cdr form)))
      ;; M60 imp-9 fix (cr.org F3, F4, F5): `let' shares the undo path
      ;; of `let*'.  Every INIT is evaluated in the OUTER environment
      ;; FIRST, then the names are bound INSIDE the `dynamic-wind' body,
      ;; so an INIT that raises restores the names that are bound
      ;; already (F3).  The restore thunks run LAST-IN-FIRST-OUT, so a
      ;; DUPLICATE name gets the outer value back (F4).  A BARE SYMBOL
      ;; binding binds elisp nil (F5).
      ((eq? head 'let)
       (let ((body (cddr form))
             (restore '()))
         (dynamic-wind
           (lambda () #t)
           (lambda ()
             (let ((inits (map elisp-loader-binding-init (cadr form))))
               (for-each (lambda (binding init)
                           (set! restore
                                 (cons (elisp-loader-bind-thunk
                                        (elisp-loader-binding-name binding)
                                        init)
                                       restore)))
                         (cadr form) inits))
             (elisp-loader-eval-seq body))
           (lambda () (for-each (lambda (thunk) (thunk)) restore)))))
      ((eq? head 'lambda)
       (elisp-loader-make-procedure (cadr form) (cddr form)))
      ;; F2 (cr.org section 4): `defun' lets a loaded file DEFINE a
      ;; function that a later form CALLS.  The definition lands in the
      ;; elisp function cell.
      ((eq? head 'defun)
       ;; M60 imp-7 fix -- L8 (cr.org F3): the `defun' must SHADOW a macro
       ;; of the same name, so the table entry is DROPPED BEFORE the
       ;; function cell is written.  Emacs has ONE cell for both forms.
       (elisp-loader-macro-drop! (cadr form))
       (set-symbol-function! (cadr form)
                             (elisp-loader-make-procedure (caddr form)
                                                          (cdddr form))))
      ;; M60 imp-6 -- row 21: `defconst' evaluates INIT and stores it in
      ;; the value cell ALWAYS.  It returns the SYMBOL, not the value:
      ;; `set-symbol-value!' returns the value, so the branch returns
      ;; `(cadr form)' explicitly.  A 3rd element (DOC) is ignored and
      ;; NOT evaluated.
      ((eq? head 'defconst)
       (set-symbol-value! (cadr form)
                          (if (pair? (cddr form))
                              (elisp-loader-eval (caddr form))
                              #nil))
       (cadr form))
      ;; M60 imp-6 -- row 22: `defvar' stores INIT ONLY when the value
      ;; cell is EMPTY.  `symbol-value' raises on an empty cell, so the
      ;; `symbol-bound?' test comes FIRST.  A `defvar' with no INIT
      ;; leaves the cell EMPTY.  It returns the SYMBOL, not the value.
      ((eq? head 'defvar)
       (let ((name (cadr form)))
         (if (and (pair? (cddr form)) (not (symbol-bound? name)))
             (set-symbol-value! name (elisp-loader-eval (caddr form))))
         name))
      ;; M60 imp-7 LIMITS of rows 23 and 24 (brief.org section 5, cr.org
      ;; F2).  These are NAMED limits, never claims:
      ;; L2 a macro call expands when the evaluator EVALUATES the call
      ;;    form, so a call inside a `defun' body expands at CALL time,
      ;;    not at definition time.
      ;; L3 the expander runs on the DYNAMIC binding model of this
      ;;    evaluator, not on the lexical model of a compiler.
      ;; L4 CLOSED at M60 imp-19 for 3 shapes: a name after `&optional'
      ;;    binds the elisp nil `#nil' when no argument is left; the name
      ;;    after `&rest' binds the whole remaining list; the walk never
      ;;    calls `(cdr args)' past the end of a short list.  The binder
      ;;    is `elisp-loader-bind-params!' and the C peer is
      ;;    `funcall_lambda' (src/eval.c :2167).
      ;; L45 a missing REQUIRED argument and an EXTRA argument do not
      ;;    raise `wrong-number-of-arguments'.  C raises it at
      ;;    src/eval.c :2224 and :2242; this loader stays lenient, so a
      ;;    file that loads today keeps loading.
      ;; L46 a malformed parameter list does NOT raise, and each shape
      ;;    has 1 answer: a bare `&rest' is IGNORED (no cell, the walk
      ;;    stops); `(a &rest &rest)' puts the remaining list in the
      ;;    cell of `&rest'; a non-symbol name raises a Guile
      ;;    `wrong-type-arg' from `symbol-bound?'.  C raises
      ;;    `invalid-function' instead (src/eval.c :2198, :2240).
      ;; L47 the binder binds DYNAMICALLY (L3), so a `&rest' value is a
      ;;    plain Scheme list, not a lexenv alist.
      ;; L48 `&key' is NOT a branch.  It takes the positional step of B4,
      ;;    so a `&key' name binds 1 argument and the walk continues.
      ;; L5 a DOC element is not stripped.  A leading string in the body
      ;;    evaluates to itself and is ignored.
      ;; L6 the table lookup adds 1 `assq' to every function call on this
      ;;    path.  No timing was taken.
      ;; M60 imp-7 -- row 24 (L1): `eval-when-compile' is a MACRO in Emacs,
      ;; but a source-reading loader has no compile phase.  At LOAD time
      ;; its body must RUN.  DECISION, not a port: this is the
      ;; INTERPRETER behaviour; a compiler drops the body.
      ((eq? head 'eval-when-compile)
       (elisp-loader-eval-seq (cdr form)))
      ;; M60 imp-12 LIMITS of row 31 (brief.org section 9).  Named
      ;; limits, never claims.  The corpus owns the row-map status.
      ;; L27 a compiler drops the body of `eval-when-compile' and runs
      ;;    the body of `eval-and-compile' 2 times.  This loader has no
      ;;    compile phase, so it runs the body ONE time for BOTH rows.
      ;; L28 the body runs under the DYNAMIC binding model of this
      ;;    evaluator (L3), not under the lexical model of a compiler.
      ;; L29 the branch does not strip a DOC string and does not warn on
      ;;    a non-macro use.
      ;; L30 the value is the value of the last body form at LOAD time.
      ;;    The return value of the BYTE-COMPILED form is out of scope.
      ;; L15 still holds: `EMPTY-CELLS' is a FIXED 11-name list, so it
      ;;    is NOT the proof of row 31.  The proof is the `subr.el' load
      ;;    line.  The NEXT wall of that file is `void-function
      ;;    (defalias)' at :29, and the `defalias' row owns that wall.
      ;; M60 imp-14: row 34 fills that cell.  The NEXT wall of
      ;;    `subr.el' is now `void-function (defsubst)' at :315, and no
      ;;    row of the map owns it.
      ;; M60 imp-12 -- row 31: `eval-and-compile' is a MACRO in Emacs.
      ;; boot.el :49 expands it to 2 nested `progn' forms, so a compiler
      ;; runs the body 2 TIMES.  A source-reading loader has no compile
      ;; phase: the body RUNS ONE time at LOAD time and the value of its
      ;; last form is the value.  DECISION, not a port (L27 ... L30).
      ((eq? head 'eval-and-compile)
       (elisp-loader-eval-seq (cdr form)))
      ;; M60 imp-7 -- row 23: `defmacro' STORES an expander and does NOT
      ;; evaluate the argument forms.  The expander goes into the macro
      ;; table above, built with the same call that `defun' makes.  The
      ;; elisp function cell is NOT touched (see the table comment), so
      ;; the `symbol-function' reader and the `fbound?' predicate stay
      ;; unaware.  The branch returns the SYMBOL.
      ;; L10 (cr.org F2): the drop is ONE-WAY.  A `defmacro' that lands
      ;; AFTER a `defun' of the same name leaves the OLD procedure in the
      ;; elisp function cell, because Emacs has 1 cell and this loader has
      ;; 2 stores.  A CALL is still correct: `else' tests the table FIRST.
      ;; Only `symbol-function' reads the stale value.  The cell is NOT
      ;; cleared, because 1 more write to the elisp function cell would
      ;; move the design counter 18 of brief.org section 9.
      ((eq? head 'defmacro)
       (set! elisp-loader-macro-table
             (acons (cadr form)
                    (elisp-loader-make-procedure (caddr form) (cdddr form))
                    elisp-loader-macro-table))
       (cadr form))
      ;; M60 imp-9 LIMITS of row 28a (brief.org section 10).  These are
      ;; NAMED limits, never claims:
      ;; L16 `cond' has no `=>' extension and no `cl-case' clause shape.
      ;;    A file that needs either is a NEW row.
      ;; L17 `while' has no loop limit.  A loaded file can loop forever.
      ;;    No limit is added here: a limit would change elisp behavior.
      ;; L18 the binding model is DYNAMIC, as for `let' (L3).  `let*'
      ;;    does not make a closure.
      ;; L19 `cond' tests the catch-all SYMBOLS `t' and `otherwise'
      ;;    WITHOUT evaluation.  An elisp file that binds `otherwise' as
      ;;    a variable gets a different result.
      ;; L20 the loader still has no `catch' / `unwind-protect' /
      ;;    `condition-case'.  Row 28b (backquote) stays OPEN.
      ;; L21 the `cond' clause-shape error is a Guile `misc-error', not
      ;;    an elisp `error' signal (cr.org F6): this loader has no
      ;;    `signal' path (L20).  The rest of the loader throws
      ;;    `void-function' / `void-variable' only.
      ;; NOTE (imp-9): L7 above holds the row-28 status AT imp-7.  Row
      ;; 28a CLOSES here; row 28b (`backquote', `,' and `,@') stays OPEN.
      ;;
      ;; M60 imp-9 -- row 28a: `cond'.  A clause is (TEST BODY ...).  The
      ;; catch-all is tested as a SYMBOL, before the evaluation of TEST,
      ;; because `t' is a variable and `otherwise' is usually unbound.
      ;; A clause with a TEST only returns the test value.  An empty
      ;; clause list and a no-match return #nil.  The elisp truth test is
      ;; `elisp-loader-truthy?', not Scheme truth: (eq? '#nil #f) is
      ;; false.
      ((eq? head 'cond)
       (let loop ((clauses (cdr form)))
         (if (null? clauses)
             #nil
             (let ((clause (car clauses)))
               (if (not (pair? clause))
                   (error "cond: clause is not a list: ~s" clause)
                   (if (memq (car clause) '(t otherwise))
                       (if (pair? (cdr clause))
                           (elisp-loader-eval-seq (cdr clause))
                           (car clause))
                       (let ((value (elisp-loader-eval (car clause))))
                         (if (elisp-loader-truthy? value)
                             (if (pair? (cdr clause))
                                 (elisp-loader-eval-seq (cdr clause))
                                 value)
                             (loop (cdr clauses))))))))))
      ;; M60 imp-9 -- row 28a: `let*'.  The bindings are made ONE AT A
      ;; TIME, so a later INIT sees the PREVIOUS name.  All INIT forms
      ;; must NOT be pre-evaluated into a list.  The undo path is the
      ;; `let' path: 1 `elisp-loader-bind-thunk' per name, the body inside
      ;; `dynamic-wind', and every restore thunk in the exit thunk.
      ;; M60 imp-9 fix (cr.org F3, F5): the bindings are made ONE AT A
      ;; TIME, so a later INIT sees the PREVIOUS name, and the loop runs
      ;; INSIDE the `dynamic-wind' body, so an INIT that raises restores
      ;; the names that are bound already (F3).  Restore runs
      ;; LAST-IN-FIRST-OUT.  A BARE SYMBOL binding binds elisp nil.
      ((eq? head 'let*)
       (let ((body (cddr form))
             (restore '()))
         (dynamic-wind
           (lambda () #t)
           (lambda ()
             (let loop ((bindings (cadr form)))
               (if (pair? bindings)
                   (begin
                     (set! restore
                           (cons (elisp-loader-bind-thunk
                                  (elisp-loader-binding-name (car bindings))
                                  (elisp-loader-binding-init (car bindings)))
                                 restore))
                     (loop (cdr bindings)))))
             (elisp-loader-eval-seq body))
           (lambda () (for-each (lambda (thunk) (thunk)) restore)))))
      ;; M60 imp-9 -- row 28a: `while'.  The TEST runs BEFORE the first
      ;; body form, so a false test runs the body 0 times.  A body of 0
      ;; forms is legal: then the loop is 1 test only.  The value is
      ;; ALWAYS #nil, also when the body ran.  A named `let' loop, not
      ;; Guile `while'.
      ((eq? head 'while)
       (let loop ()
         (if (elisp-loader-truthy? (elisp-loader-eval (cadr form)))
             (begin (elisp-loader-eval-seq (cddr form)) (loop))
             #nil)))
      ;; M60 imp-20 -- row 36: `declare' is DATA for the byte compiler.
      ;; This loader has no compile phase, so it IGNORES the form.  No
      ;; branch of the map owned the name: the tree defines no `declare'
      ;; (0 `defmacro declare' in lisp/; src/eval.c has no DEFUN and no
      ;; code branch), and `byte-run.el' :323 reads the form as a body
      ;; MARK.  The reachable shape is a DECLARATION BODY FORM of a
      ;; `defmacro' expander, not a top-level form:
      ;; `define-obsolete-function-alias' (:559) is the first one that a
      ;; loaded file reaches.  DECISION, not a port.
      ;; LIMITS of this row.  These are NAMED limits, never claims:
      ;; L49 the CONTENT of a `(declare ...)' form is NOT stored.  No
      ;;    indenter mark, no `debug' spec, no `pure' /
      ;;    `side-effect-free' flag, no `obsolete' mark.
      ;; L50 there is no warning channel (L11 ... L13, defined in
      ;;    utils.scm :607), so a `(declare (obsolete ...))' form
      ;;    produces NO warning.
      ;; L51 there is no SHAPE check.  `(declare)', `(declare a b)' and a
      ;;    dotted form all return the elisp nil and never raise.  The
      ;;    branch also SHADOWS a macro named `declare': it is tested
      ;;    BEFORE the macro table, so such an expander can never run.
      ;;    No file of lisp/ defines that macro.
      ;; L52 `declare-function', `cl-declare' and the `:documentation'
      ;;    mark are OTHER names.  This branch does not cover them.
      ;; The form is UNEVALLED: no element of it is evaluated (L51).
      ((eq? head 'declare) #nil)
      (else
       ;; M60 imp-7 -- row 23: the macro table is tested BEFORE the
       ;; function cell.  The expander gets the UNEVALUATED argument
       ;; forms, and the evaluator evaluates the expansion.  L7 Row 28 (the
       ;; expansion path: backquote, ,@, cond, let*, while) stays OPEN.
       (let ((expander (elisp-loader-macro-ref head)))
         (if expander
             (elisp-loader-eval (apply expander (cdr form)))
             (if (symbol-fbound? head)
                 ;; M60 imp-14 -- row 34: pass the HEAD SYMBOL, not
                 ;; (symbol-function head).  `elisp-loader-apply' follows
                 ;; the whole cell chain (C `indirect_function'), so a
                 ;; PRE-RESOLVED cell loses the name that the caller
                 ;; wrote: a ring A -> B -> A would name `b' in the
                 ;; `cyclic-function-indirection' raise.
                 (elisp-loader-apply head
                                     (map elisp-loader-eval (cdr form)))
                 (throw 'void-function head))))))))

;; The elisp compiler is C (row 10).  When lookup-language raises
;; misc-error with the "no such language" message, the C compiler is
;; absent: return #f so load-elisp-full takes the source-reading branch.
;; Keep the language object otherwise.
;;
;; F6 (cr.org section 4): catch ONLY the "no such language" case.  Any
;; other misc-error (a real error) is RE-RAISED, so it can not silently
;; take the source-reading branch.
;; M60 imp-3: the presence of the language object does NOT prove that a
;; compiled elisp form can RUN.  The bytecode resolves its variables in
;; the `elisp-symbols' module, and only the C core fills that module
;; (MEASURED: a compiled test/mod fixture raises `Unbound variable: n',
;; and a compiled lisp/ file raises `Unbound variable: mapcar').  So the
;; test below also requires the C runtime handoff of `emacs!' (see
;; `c-runtime-installed?').  Before the split the absent language hid
;; this gap; it is now explicit.
(define (elisp-loader-compiler-available?)
  (catch 'misc-error
    (lambda () (if (c-runtime-installed?) (lookup-language 'emacs-elisp) #f))
    (lambda (key . args)
      (if (any (lambda (arg)
                 (and (string? arg) (string-contains arg "no such language")))
               args)
          #f
          (apply throw key args)))))

;; Read and evaluate SRC when the elisp compiler is absent.  The port is
;; closed also on error (dynamic-wind), like the C unwind-protect.
(define (elisp-load-source-file src)
  (let ((port (open-input-file src)))
    (dynamic-wind
      (lambda () #t)
      (lambda () (elisp-load-read-eval-loop-from-port port #f))
      (lambda () (close-port port)))))

(define (init-loader prelude-directory)
  (set-current-module (resolve-module '(emacs-elisp runtime)))
  (let* ((str (canonicalize-path (string-concatenate (list prelude-directory "/.."))))
         (dirs (list (string-concatenate (list str "/lisp"))
                     (string-concatenate (list str "/lisp/emacs-lisp"))
                     (string-concatenate (list str "/lisp/progmodes"))
                     (string-concatenate (list str "/lisp/language"))
                     (string-concatenate (list str "/lisp/international"))
                     (string-concatenate (list str "/lisp/textmodes"))
                     (string-concatenate (list str "/lisp/vc"))
                     (string-concatenate (list str "/lisp/mail"))
                     (string-concatenate (list str "/lisp/url"))
                     (string-concatenate (list str "/lisp/gnus"))
                     (string-concatenate (list str "/lisp/net"))
                     (string-concatenate (list str "/lisp/calendar"))
                     (string-concatenate (list str "/lisp/cedet"))
                     (string-concatenate (list str "/lisp/eshell")))))
    (set! %load-path (append dirs %load-path))
    ;; M55 imp-2: the runtime cells read these elisp variables through
    ;; `symbol-value'.  In a plain `guile' process they are UNBOUND
    ;; (measured); the C bootstrap binds them in a full Emacs.  Bind the
    ;; Emacs defaults only when absent, so the full-Emacs values stay.
    ;; FIX-20261014-guilemacs: this default binding is a standalone-load
    ;; workaround.  Remove it once the C bootstrap binds these variables.
    (unless (symbol-bound? 'load-path)
      (set-symbol-value! 'load-path dirs))
    (unless (symbol-bound? 'load-suffixes)
      (set-symbol-value! 'load-suffixes (list ".el")))
    (unless (symbol-bound? 'load-file-rep-suffixes)
      (set-symbol-value! 'load-file-rep-suffixes (list "")))
    ;; M55 imp-4: the reader reads `load-read-function' through
    ;; symbol-value (mod/emacs/reader.scm elisp-read-with-load-function-
    ;; from-port).  Emacs pre-binds it to nil.  In a plain `guile' process
    ;; it is absent, and the Scheme symbol-value returns Guile's UNBOUND
    ;; sentinel (not #nil), so the reader would treat the sentinel as a
    ;; real read function and apply the empty `funcall' cell (measured).
    ;; Bind the Emacs default only when absent.
    ;; FIX-20261015-guilemacs: standalone-load workaround; remove once the
    ;; C bootstrap binds this variable.
    (unless (symbol-bound? 'load-read-function)
      (set-symbol-value! 'load-read-function #nil))
    ;; M60 imp-4 — row 19: `features' is a C DEFVAR_LISP (src/fns.c
    ;; :6372).  Bind the Emacs default only when absent.
    ;; FIX-20261020-guilemacs: standalone-load default; remove it when
    ;; the C bootstrap binds this variable.
    (unless (symbol-bound? 'features)
      (set-symbol-value! 'features '()))
    ;; M60 imp-4 — row 18: the pure cell of (emacs utils) :211.  A full
    ;; Emacs already owns the C DEFUN (src/fns.c :3450), so the guard
    ;; keeps that cell.
    (unless (symbol-fbound? 'provide)
      (set-symbol-function! 'provide elisp-provide))
    ;; M60 imp-5 — row 20: the cell of (emacs loader) :915.  A full Emacs
    ;; already owns the C DEFUN (src/fns.c :3496), so the guard keeps it.
    (unless (symbol-fbound? 'require)
      (set-symbol-function! 'require elisp-require))
    ;; M60 imp-5 — the 2 cells of the elisp `load' protocol that `require'
    ;; applies.  MEASURED: `elisp-load' reached them through
    ;; `elisp-process-load-file-path' (:246 ... :260) and stopped with
    ;; `wrong-type-arg "Wrong type to apply: #nil"' because both function
    ;; cells are EMPTY in a plain `guile' process.  `string-suffix-p'
    ;; reuses the pure-Scheme definition of (emacs strings) :336;
    ;; `file-name-directory' is the small loader split (:991).  A full
    ;; Emacs keeps the 2 C DEFUNs.
    (unless (symbol-fbound? 'string-suffix-p)
      (set-symbol-function! 'string-suffix-p elisp-string-suffix-p))
    (unless (symbol-fbound? 'file-name-directory)
      (set-symbol-function! 'file-name-directory
                            elisp-loader-file-name-directory))
    ;; M60 imp-8 -- row 27: the cell of (emacs utils), the row-18 pattern
    ;; of `provide' above: 1 install site, 1 guard, 0 new evaluator
    ;; branches.  A full Emacs already owns this cell, because
    ;; lisp/emacs-lisp/byte-run.el is preloaded.  L15: the `EMPTY-CELLS'
    ;; list of test/m60/probe-imp3.scm is a FIXED list of 11 guarded
    ;; names and does NOT hold this name, so that line is not the proof
    ;; of row 27.  The proof is the `LOAD lisp/obarray.el: done' line and
    ;; the return value and the mark that mode `obsolete' prints.
    (unless (symbol-fbound? 'make-obsolete-variable)
      (set-symbol-function! 'make-obsolete-variable
                            elisp-make-obsolete-variable))
    ;; M60 imp-16 -- row 25: the cell of (emacs utils), the row-18 pattern
    ;; of `provide' (:1533) and `make-obsolete-variable' (:1560): 1
    ;; install site, 1 guard, 0 new evaluator branches, 0 FIX markers.
    ;; The owner is the elisp Lisp function of lisp/startup.el :479, and
    ;; the 1 caller is lisp/subdirs.el :3.  That caller BINDS
    ;; `default-directory' to the directory of the file (startup.el
    ;; :631); the port reads it and never binds it (limit L42), so this
    ;; guard does NOT bind it -- a default here would hide the missing
    ;; caller bind.  A full Emacs already owns this cell, because
    ;; `startup.el' loads before any `subdirs.el' load; the guard keeps
    ;; the elisp `defun'.
    ;; MEASURED (`guile -L mod', GUILE_AUTO_COMPILE=0, mode `subdirs' in
    ;; test/m60/probe-imp3.scm): `lisp/subdirs.el' :3 names 24
    ;; subdirectories, all 24 exist in this tree, and `load-path' goes
    ;; 14 -> 38, with the new entry after the `<root>/lisp' anchor at
    ;; index 0 being `<root>/lisp/vc'.  milestone.org section 4 says 21;
    ;; that value does not reproduce.
    ;; Limits: L39 ... L43, named at the definition in (emacs utils).
    (unless (symbol-fbound? 'normal-top-level-add-to-load-path)
      (set-symbol-function! 'normal-top-level-add-to-load-path
                            elisp-normal-top-level-add-to-load-path))
    ;; M60 imp-17 -- F3, the row of milestone.org section 3: the cell of
    ;; (emacs utils) :493, the row-18 pattern of `provide' (:1533) and
    ;; `make-obsolete-variable' (:1560): 1 install site, 1 guard, 0 new
    ;; evaluator branches, 0 FIX markers.  The C owner is
    ;; `DEFUN ("featurep", Ffeaturep, Sfeaturep, 1, 2, 0)' at
    ;; src/fns.c :3432.  A full Emacs already owns that cell, so this
    ;; guard keeps the C DEFUN there.
    ;; The old site was UNGUARDED: `utils.scm' :975 inside
    ;; `init-utils-registrations' (:960), a function that this
    ;; `init-loader' does not call.  The deletion therefore changes no
    ;; other path.
    ;; Truth values: `elisp-featurep' answers `#t' or `#nil'.
    ;; `(eq? #nil #f)' is FALSE, so a condition that comes from this
    ;; cell must pass through `elisp-loader-truthy?' (:1072).
    ;; L15: `EMPTY-CELLS' of test/m60/probe-imp3.scm is a FIXED list of
    ;; 11 guarded names and does NOT hold `featurep', so that line is
    ;; not the proof of F3.  The proof is the `featurep-fbound' line of
    ;; that fixture.
    (unless (symbol-fbound? 'featurep)
      (set-symbol-function! 'featurep elisp-featurep))
    ;; M60 imp-18 -- row 35: the row-18 pattern of `provide' (:1533)
    ;; and `make-obsolete-variable' (:1560): 1 install site, 1 guard,
    ;; 0 new evaluator branches, 0 FIX markers.  The C owner is
    ;; `DEFUN ("bare-symbol", Fbare_symbol, Sbare_symbol, 1, 1, 0)' at
    ;; src/data.c :599; a full Emacs keeps that cell.
    ;; The argument vector 1, 1, 0 names NO type predicate, so the C
    ;; function is the identity and raises no `wrong-type-argument'.
    ;; The port (types.scm :426) copies that shape: it answers its
    ;; argument for a symbol, a number and `#nil' alike.
    (unless (symbol-fbound? 'bare-symbol)
      (set-symbol-function! 'bare-symbol elisp-bare-symbol)))
  (set! %load-extensions (cons ".el" %load-extensions))

  (set-symbol-function! 'load elisp-load)
  (set-symbol-function! 'autoload-do-load elisp-autoload-do-load)

  ;; M55 imp-2: the 7 reachable runtime cells, in call order (rows 3 ...
  ;; 9 of docs/m55-plan.org section 3.2), with no C fallback.
  ;;
  ;; F6 (cr.org section 4, item 7): install a cell ONLY when it is empty.
  ;; In the full Emacs the C core already owns `expand-file-name'
  ;; (src/fileio.x) and `file-directory-p'; the imp-2 Scheme cells handle
  ;; the load-path case only, so an unconditional install would replace
  ;; the C cell for EVERY elisp caller.  `symbol-fbound?' keeps the C
  ;; cell.  In a plain `guile' process every cell is empty, so all 7
  ;; install (measured: test/m55/test-m55-imp2.el group S2).
  (unless (symbol-fbound? 'get-load-suffixes)
    (set-symbol-function! 'get-load-suffixes elisp-get-load-suffixes))
  (unless (symbol-fbound? 'append)
    (set-symbol-function! 'append elisp-append))
  (unless (symbol-fbound? 'symbol-value)
    (set-symbol-function! 'symbol-value symbol-value))
  (unless (symbol-fbound? 'car)
    (set-symbol-function! 'car elisp-car))
  (unless (symbol-fbound? 'expand-file-name)
    (set-symbol-function! 'expand-file-name elisp-loader-expand-file-name))
  (unless (symbol-fbound? 'file-directory-p)
    (set-symbol-function! 'file-directory-p elisp-loader-file-directory-p))
  (unless (symbol-fbound? 'cdr)
    (set-symbol-function! 'cdr elisp-cdr))

  ;; M55 imp-4: the reader cells and the eval cell, in call order
  ;; (brief.org section 6).  In a plain `guile' process the reader applies
  ;; `intern' 18 times, `concat' 2 times, and `substring' 1 time; the
  ;; read-eval loop applies `eval' on every form.  Every cell is empty
  ;; there.  No C fallback: `intern' reuses the pure-Scheme elisp-intern;
  ;; `concat' and `substring' are small Scheme procedures; `eval' is the
  ;; minimal Scheme evaluator (elisp-loader-eval).  The `symbol-fbound?'
  ;; guard keeps a C cell in a full Emacs.
  (unless (symbol-fbound? 'intern)
    (set-symbol-function! 'intern elisp-intern))
  (unless (symbol-fbound? 'concat)
    (set-symbol-function! 'concat elisp-loader-concat))
  (unless (symbol-fbound? 'substring)
    (set-symbol-function! 'substring elisp-loader-substring))
  (unless (symbol-fbound? 'eval)
    (set-symbol-function! 'eval elisp-loader-eval))

  ;; M60 imp-10 -- row 29: the comparison and arithmetic cells, plus
  ;; `length' and `nreverse'.  MEASURED with mode `arith' of
  ;; test/m60/probe-imp3.scm: all 15 names are EMPTY in a plain `guile'
  ;; process, and `lisp/color.el' stops at `void-function (/)' before
  ;; this row.  Every name is 1 GUARDED install of an EXISTING
  ;; pure-Scheme definition:
  ;;
  ;;   (emacs types)     elisp-null :147, elisp-eq :174, elisp-eql :178,
  ;;                     elisp-equal :209
  ;;   (emacs numbers)   elisp-+ :76, elisp-- :79, elisp-* :82,
  ;;                     elisp-/ :91, elisp-1+ :104, elisp-1- :107, and
  ;;                     the `let-syntax' block at :126 for elisp-=,
  ;;                     elisp-< and elisp->
  ;;   (emacs sequences) elisp-length :297
  ;;   (emacs utils)     elisp-nreverse :340
  ;;
  ;; The guard is the row-18 pattern: a full Emacs already owns the C
  ;; DEFUN (src/data.c, src/fns.c) in that cell.
  ;;
  ;; The bulk installers `init-types-registrations',
  ;; `init-numbers-registrations' (numbers.scm :290) and
  ;; `init-utils-registrations' (utils.scm :888) install with NO guard,
  ;; so they overwrite the C cell.
  ;; `init-utils-registrations' :904 is the UNGUARDED install of
  ;; `nreverse'; it is not called on this path, and this row does not
  ;; call it either.
  ;;
  ;; L24: `<=' and `>=' are NOT in the row-29 name list of
  ;; milestone.org section 3, so they stay EMPTY here and a later row
  ;; owns them.  Their definitions do exist (numbers.scm :126).
  ;;
  ;; The elisp truth values: elisp-eq, elisp-eql, elisp-equal,
  ;; elisp-null and the 5 comparison procedures return #t or #nil, and
  ;; `(eq? '#nil #f)' is FALSE.  A condition that comes from one of
  ;; these cells MUST pass through `elisp-loader-truthy?' (:1062).
  (unless (symbol-fbound? 'eq)
    (set-symbol-function! 'eq elisp-eq))
  (unless (symbol-fbound? 'eql)
    (set-symbol-function! 'eql elisp-eql))
  (unless (symbol-fbound? 'equal)
    (set-symbol-function! 'equal elisp-equal))
  (unless (symbol-fbound? 'null)
    (set-symbol-function! 'null elisp-null))
  (unless (symbol-fbound? '+)
    (set-symbol-function! '+ elisp-+))
  (unless (symbol-fbound? '-)
    (set-symbol-function! '- elisp--))
  (unless (symbol-fbound? '*)
    (set-symbol-function! '* elisp-*))
  (unless (symbol-fbound? '/)
    (set-symbol-function! '/ elisp-/))
  (unless (symbol-fbound? '=)
    (set-symbol-function! '= elisp-=))
  (unless (symbol-fbound? '<)
    (set-symbol-function! '< elisp-<))
  (unless (symbol-fbound? '>)
    (set-symbol-function! '> elisp->))
  (unless (symbol-fbound? '1+)
    (set-symbol-function! '1+ elisp-1+))
  (unless (symbol-fbound? '1-)
    (set-symbol-function! '1- elisp-1-))
  (unless (symbol-fbound? 'length)
    (set-symbol-function! 'length elisp-length))
  (unless (symbol-fbound? 'nreverse)
    (set-symbol-function! 'nreverse elisp-nreverse))

  ;; M60 imp-11 -- row 30: `put' is the FIRST stop of
  ;; lisp/calendar/time-date.el (MEASURED: void-function (put)).  The
  ;; caller is lisp/emacs-lisp/macroexp.el :137, through the `require'
  ;; of cl-lib (cl-lib.el :87 requires macroexp); time-date.el itself
  ;; calls no `put'.  The pure definition is `elisp-put'
  ;; (utils.scm :169), and (emacs utils) is imported as a WHOLE module
  ;; at :19, so this row adds 1 GUARDED install and NO procedure and NO
  ;; import.
  ;;
  ;; The guard is the row-18 pattern: a full Emacs owns the C DEFUN
  ;; (src/fns.c, Fput) in that cell.  The bulk installer
  ;; `init-utils-registrations' (utils.scm :888) also writes `put' at
  ;; :900, but with NO guard, and `init-loader' does not call it.
  ;;
  ;; L26: `put' returns the VALUE, and a STRING or a NUMBER first
  ;; argument raises `Wrong type argument: symbolp'.  Both are elisp
  ;; behaviour, so mode `put' of test/m60/probe-imp3.scm pins them.
  ;;
  ;; The NEXT stop after this row was `make-hash-table' at
  ;; lisp/emacs-lisp/macroexp.el :165.  Row 32 installed that family in
  ;; the block below (M60 imp-15), so the stop moved.
  (unless (symbol-fbound? 'put)
    (set-symbol-function! 'put elisp-put))

  ;; M60 imp-13 -- row 33: `set' is the cell of the reader keyword path
  ;; (reader.scm :1358) and of the `values' loops (:132, :227).  The
  ;; guard is the row-18 pattern: a full Emacs owns the C DEFUN cell
  ;; (src/data.c :1317).  The bulk installer `init-utils-registrations'
  ;; writes cells with NO guard, so this row does not use it.  Proof is
  ;; mode `set' of test/m60/probe-imp3.scm; `EMPTY-CELLS' (L15) is a
  ;; fixed 11-name list and does not cover `set'.  The not-ported
  ;; branches are at the definition (utils.scm :195).
  (unless (symbol-fbound? 'set)
    (set-symbol-function! 'set elisp-set))

  ;; M60 imp-14 -- row 34: `defalias' is form 2 of `lisp/subr.el' (:29),
  ;; inside the `eval-and-compile' of :28.  The C owner is `Fdefalias'
  ;; (src/data.c :706).  The guard is the row-18 pattern: a full Emacs
  ;; owns the C DEFUN cell.  The bulk installer
  ;; `init-utils-registrations' writes cells with NO guard, so this row
  ;; does not use it.
  ;;
  ;; The cell holds the DEFINITION as written: `defalias' does NOT
  ;; resolve a symbol.  `elisp-loader-apply' follows the chain at CALL
  ;; time (C `indirect_function'), so `(symbol-function 'string=)' is the
  ;; SYMBOL `string-equal' and `(string= "a" "a")' is still t.
  ;;
  ;; L31 ... L35 are named at the 2 definitions: L31 (macro table), L32
  ;; (`defalias-fset-function' hook), L33 (pure copy) and L34 (load
  ;; history) at `elisp-defalias' (utils.scm :235), L35 (a `(closure ...)'
  ;; literal ARG) at the `function' branch of `elisp-loader-eval-form'.
  ;;
  ;; Proof is mode `alias' of test/m60/probe-imp3.scm and 2 cases of
  ;; test/mod/standalone-tests.scm; `EMPTY-CELLS' (L15) is a fixed
  ;; 11-name list and does not cover `defalias'.
  (unless (symbol-fbound? 'defalias)
    (set-symbol-function! 'defalias elisp-defalias))

  ;; M60 imp-15 -- row 32: the `make-hash-table' family.  The C owners
  ;; are the 12 DEFUNs of src/fns.c :5253 ... :5491; `hash-table-keys'
  ;; and `hash-table-values' have no C DEFUN, so they are pure-Scheme
  ;; cells of utils.scm.  The first real caller is the `defvar' of
  ;; `macroexp--warned' at lisp/emacs-lisp/macroexp.el :165.  The guard
  ;; is the row-18 pattern: a full Emacs owns the C DEFUN cells.
  ;;
  ;; TWO bulk installers write hash cells with NO guard:
  ;; `init-utils-registrations' (utils.scm :888) writes
  ;; `hash-table-count' and `clrhash', and `init-types-registrations'
  ;; (types.scm :503) writes `hash-table-p' (:510).  So this row does not
  ;; use them: each of the 14 names has ONE install site, the guarded
  ;; block below.
  ;;
  ;; 1 SRFI-69 table IS the elisp object, so `hash-table-p' is the
  ;; existing `elisp-hash-table-p' of types.scm :444.  The 2 LIMITS are
  ;; named at the definitions (utils.scm :274 ... :297 section): L37 (a
  ;; valid `:weakness' is parsed and IGNORED, every table is STRONG) and
  ;; L38 (`hash-table-size' answers the entry count, C answers the
  ;; allocation size).  Proof is mode `hash' of test/m60/probe-imp3.scm
  ;; and the row-32 cases of test/mod/standalone-tests.scm.
  ;;
  ;; MEASURED after the 14 installs: `lisp/emacs-lisp/macroexp.el' passes
  ;; form 2 (:165) and stops on the NEXT wall,
  ;; `void-function (define-obsolete-function-alias)'.
  (unless (symbol-fbound? 'make-hash-table)
    (set-symbol-function! 'make-hash-table elisp-make-hash-table))
  (unless (symbol-fbound? 'gethash)
    (set-symbol-function! 'gethash elisp-gethash))
  (unless (symbol-fbound? 'puthash)
    (set-symbol-function! 'puthash elisp-puthash))
  (unless (symbol-fbound? 'remhash)
    (set-symbol-function! 'remhash elisp-remhash))
  (unless (symbol-fbound? 'clrhash)
    (set-symbol-function! 'clrhash elisp-clrhash))
  (unless (symbol-fbound? 'hash-table-p)
    (set-symbol-function! 'hash-table-p elisp-hash-table-p))
  (unless (symbol-fbound? 'hash-table-count)
    (set-symbol-function! 'hash-table-count elisp-hash-table-count))
  ;; The 7 accessor cells.  An elisp file that calls
  ;; `(hash-table-size table)' or `(hash-table-test table)' reads THESE
  ;; cells, not a `module-ref'.
  (unless (symbol-fbound? 'hash-table-test)
    (set-symbol-function! 'hash-table-test elisp-hash-table-test))
  (unless (symbol-fbound? 'hash-table-weakness)
    (set-symbol-function! 'hash-table-weakness elisp-hash-table-weakness))
  (unless (symbol-fbound? 'hash-table-size)
    (set-symbol-function! 'hash-table-size elisp-hash-table-size))
  (unless (symbol-fbound? 'hash-table-keys)
    (set-symbol-function! 'hash-table-keys elisp-hash-table-keys))
  (unless (symbol-fbound? 'hash-table-values)
    (set-symbol-function! 'hash-table-values elisp-hash-table-values))
  (unless (symbol-fbound? 'hash-table-rehash-size)
    (set-symbol-function! 'hash-table-rehash-size
                          elisp-hash-table-rehash-size))
  (unless (symbol-fbound? 'hash-table-rehash-threshold)
    (set-symbol-function! 'hash-table-rehash-threshold
                          elisp-hash-table-rehash-threshold))
  )
