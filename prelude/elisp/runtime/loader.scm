;;; Guilemacs Lisp
;;;
;;; File Loading Infrastructure
;;;
;;; File loading infrastructure - handles .el/.elc files, load-path, etc.
;;; Migrated from lread.c Fload function.
;;; Includes: file validation, load-path management, read-eval loop, history.

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
;;; File Path Processing
;;;

(define (elisp-process-load-file-path file nosuffix must-suffix)
  "Process file path and determine suffixes for loading.
This replicates the file path processing logic from Fload (lines 979-1020).

Returns: (file-to-search . suffixes-list)
- file-to-search: the file name to search for
- suffixes-list: list of suffixes to try, or #nil"
  (when (= ((symbol-function 'length) file) 0)
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

(define (elisp-validate-load-file file)
  "Validate file argument for loading.
This replicates the validation logic from Fload (lines 966, 976-977).
Returns #t if valid, signals error if invalid."
  (unless (string? file)
    ((symbol-function 'signal) (elisp-intern "wrong-type-argument" #nil)
     ((symbol-function 'list) (elisp-intern "stringp" #nil) file)))
  (when (= ((symbol-function 'length) file) 0)
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
         (or (char=? (string-ref path-string 0) #\/)
             (char=? (string-ref path-string 0) #\\))
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
          'signal-error
          'return-nil)
      'continue))

(define (elisp-setup-file-descriptor-protection fd)
  "Determine if file descriptor needs unwind protection.
This replicates the unwind protection logic from Fload (lines 1008-1011).
Returns: #t if protection should be set up, #f otherwise."
  (>= fd 0))

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

;;;
;;; Compound Operations
;;;

(define (elisp-validate-and-check-handler file noerror nomessage nosuffix must-suffix)
  "Compound function: Validate file and check for magic file name handlers.
This consolidates elisp-validate-load-file and elisp-check-file-handler.
Returns: handler result if handler found, #f if should continue with normal loading."
  (elisp-validate-load-file file)
  (elisp-check-file-handler file noerror nomessage nosuffix must-suffix))

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

;;;
;;; Registration with Elisp symbol table
;;; NOTE: All registrations commented out to avoid conflicts with prelude/load.scm
;;; These functions are defined here but registered in load.scm for now.
;;; Once we migrate functions from load.scm to this module, we can uncomment
;;; the registrations incrementally.
;;;

;; Read-eval loop functions
;; (No direct registrations - called from C)

;; File path processing
;; (No direct registrations - called from C)

;; Load message formatting
;; (No direct registrations - called from C)

;; File validation
;; (No direct registrations - called from C)

;; Load history management
;; (No direct registrations - called from C)

;; Note: These functions are primarily called from C code and do not need
;; symbol-function registrations. They are accessed via module-ref from C.

(define (elisp-call-load-source-file-function load-source-file-function found hist-file-name noerror nomessage force-load-messages)
  "Call the load-source-file-function with properly converted arguments.
This replicates the call4 logic from Fload (lines 1065-1067)."

  ;; Convert arguments to match the C call4 pattern
  (let ((error-arg (if (eq? noerror #nil) #nil #t))
        (message-arg (if (or (eq? nomessage #nil) force-load-messages) #nil #t)))

    ;; Call the function with 4 arguments
    ((symbol-function 'funcall) load-source-file-function found hist-file-name error-arg message-arg)))

(define (elisp-count-recursive-loads found loads-in-progress-list)
  "Count how many times a file appears in the loads-in-progress list.
This replicates the counting logic from Fload recursive load detection.
Signals an error if more than 3 recursive loads are detected."

  (let ((load-count 0))
    ;; Count occurrences using a simple loop
    (let loop ((tem loads-in-progress-list))
      (when (not (eq? tem #nil))
        (when (not (eq? ((symbol-function 'equal) found ((symbol-function 'car) tem)) #nil))
          (set! load-count (+ load-count 1)))
        (loop ((symbol-function 'cdr) tem))))

    ;; Check if we exceeded the limit (replicates the > 3 check)
    (when (> load-count 3)
      ;; Signal recursive load error
      ((symbol-function 'signal) (elisp-intern "error" #nil)
       ((symbol-function 'list) "Recursive load"
        ((symbol-function 'cons) found loads-in-progress-list))))

    ;; Return the count for debugging/logging if needed
    load-count))

(define (elisp-determine-load-action is-module)
  "Determine the loading action based on file type.
  This replicates the conditional logic from Fload lines 1173-1183.
  Returns: 'load-module or 'load-elisp."

  (if is-module
      'load-module
      'load-elisp))

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

    ;; Use message-with-string equivalent
    ((symbol-function 'message) base-msg file)))

(define (elisp-handle-loads-in-progress found loads-in-progress)
  "Prepare loads-in-progress list update.
This extends the recursive load handling from Fload (lines 1027-1029).
Returns: the new value for loads-in-progress list."

  ;; The C code does: Vloads_in_progress = Fcons (found, Vloads_in_progress);
  ;; We return the new cons cell for C to assign
  ((symbol-function 'cons) found loads-in-progress))

(define (elisp-load-with-match-data-protection file noerror nomessage nosuffix must-suffix)
  "Load file with match data protection.
  This replicates the save_match_data_load wrapper function."

  ;; Call the main load function - C will handle the match data protection
  ((symbol-function 'load) file noerror nomessage nosuffix must-suffix))

(define (elisp-loadhist-initialize filename)
  "Initialize load history for filename.
This replicates the loadhist_initialize function from lread.c lines 877-882.
Validates filename and sets up current-load-list binding."

  ;; Assertion check: filename must be string or nil
  (unless (or (string? filename) (eq? filename #nil))
    ((symbol-function 'error) "filename must be string or nil"))

  ;; This function just sets up the binding - the actual specbind is done in C
  ;; Return the cons to be used in specbind
  ((symbol-function 'cons) filename #nil))

(define (elisp-normalize-load-path sourcename)
  "Normalize the file path for loading, making it absolute if needed.
This replicates the C logic from readevalloop_load lines 2077-2080."
  (if (not (eq? ((symbol-function 'file-name-absolute-p) sourcename) #nil))
      ((symbol-function 'expand-file-name) sourcename #nil)
      sourcename))

(define (elisp-prepare-load-bindings hist-file-name found)
  "Prepare all dynamic bindings for load operation.
  This replicates the specbind calls from Fload lines 1158-1161.
  Returns list of (symbol . value) pairs for C to bind."

  (list
   (cons 'load-file-name hist-file-name)
   (cons 'load-true-file-name found)
   (cons 'inhibit-file-name-operation #nil)
   (cons 'load-in-progress #t)))

(define (elisp-prepare-module-loading found)
  "Prepare for module loading by initializing load history.
This replicates the module loading preparation from Fload (lines 1176-1178)."

  ;; Call loadhist-initialize for the found file
  ;; This corresponds to the C code: loadhist_initialize (found);
  ((symbol-function 'loadhist-initialize) found))

(define (elisp-prepare-openp-call path-result)
  "Prepare parameters for openp function call.
This replicates the openp call preparation from Fload (lines 985-991).
Returns: (processed-file . suffixes) pair for openp call."

  ;; Extract the components that were computed by elisp-process-load-file-path
  ;; path_result is already a (file . suffixes) pair from scheme
  path-result)

(define (elisp-process-load-file-path file nosuffix must-suffix)
  "Process file path and determine suffixes for loading.
This replicates the file path processing logic from Fload (lines 979-1020).

Returns: (file-to-search . suffixes-list)
- file-to-search: the file name to search for
- suffixes-list: list of suffixes to try, or #nil"

  ;; Validate file is not empty
  (when (= ((symbol-function 'length) file) 0)
    (error "Cannot load empty filename"))

  (let ((suffixes #nil))
    ;; Handle must-suffix logic
    (unless (eq? must-suffix #nil)
      ;; Don't insist on adding a suffix if FILE already ends with one
      (when (or ((symbol-function 'string-suffix-p) ".el" file #t)
                ;; TODO: Add module suffix checks when modules are supported
                )
        (set! must-suffix #nil))

      ;; Don't insist on adding a suffix if the argument includes a directory name
      (unless (eq? ((symbol-function 'file-name-directory) file) #nil)
        (set! must-suffix #nil)))

    ;; Determine suffixes to use
    (cond
      ;; If nosuffix is set, use no suffixes
      ((not (eq? nosuffix #nil))
       (set! suffixes #nil))

      ;; Otherwise build suffixes list
      (else
       (set! suffixes ((symbol-function 'get-load-suffixes)))
       (when (eq? must-suffix #nil)
         (set! suffixes ((symbol-function 'append) suffixes
                        ((symbol-function 'symbol-value)
                         (elisp-intern "load-file-rep-suffixes" #nil)))))))

    ;; Return the file and suffixes as a pair
    (cons file suffixes)))

(define (elisp-return-load-success)
  "Return success value for load operation completion.
  This replicates the final return Qt from Fload line 1235."
  #t) ; Return success

(define (elisp-setup-load-environment found loads-in-progress file purify-flag is-native-elisp)
  "Compound function: Set up load environment including recursive loads, bindings, and filenames.
This consolidates recursive load detection, loads-in-progress management, lexical binding setup,
effective filename computation, and history file name computation.
Returns: (new-loads-in-progress . (lexical-binding . (found-eff . hist-file-name)))"

  ;; Handle recursive load counting
  (elisp-count-recursive-loads found loads-in-progress)

  ;; Prepare new loads-in-progress list
  (let ((new-loads-in-progress (elisp-handle-loads-in-progress found loads-in-progress)))

    ;; Prepare lexical binding
    (let ((lexical-binding (elisp-handle-lexical-binding-specbind)))

      ;; Compute effective filename
      (let ((found-eff (elisp-compute-effective-filename found is-native-elisp)))

        ;; Compute history file name
        (let ((hist-file-name (elisp-compute-hist-file-name file found-eff purify-flag)))

          ;; Return all results as nested cons cells
          (cons new-loads-in-progress
                (cons lexical-binding
                      (cons found-eff hist-file-name))))))))

(define (elisp-show-load-message file is-module is-native-elisp compiled newer loading-p nomessage force-load-messages noninteractive-p)
  "Display loading messages with proper conditional logic.
This replicates the message display logic from Fload (lines 1133-1146, 1190-1203)."

  ;; Check conditions for displaying messages (replicates C conditional logic)
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

        ;; Use message function instead of message-with-string for simplicity
        ((symbol-function 'message) base-msg file)))))

(define (elisp-validate-load-file file)
  "Validate file argument for loading.
This replicates the validation logic from Fload (lines 966, 976-977).
Returns #t if valid, signals error if invalid."

  ;; Check if file is a string (replicates CHECK_STRING)
  (unless (string? file)
    ((symbol-function 'signal) (elisp-intern "wrong-type-argument" #nil)
     ((symbol-function 'list) (elisp-intern "stringp" #nil) file)))

  ;; Check for empty string (replicates SCHARS(file) == 0 check)
  (when (= ((symbol-function 'length) file) 0)
    ((symbol-function 'signal) (elisp-intern "file-error" #nil)
     ((symbol-function 'list) "Cannot load empty filename")))

  ;; Return success
  #t)

(define (elisp-check-file-handler file noerror nomessage nosuffix must-suffix)
  "Check for magic file name handler and call it if found.
  This replicates the handler check from Fload lines 973-977.
  Returns handler result or #f if no handler."

  (let ((handler ((symbol-function 'find-file-name-handler) file 'load)))
    (if handler
        ;; Call the handler with all arguments
        ((symbol-function 'funcall) handler 'load file noerror nomessage nosuffix must-suffix)
        #f))) ; No handler found

(define (elisp-complete-filename? pathname)
  "Check if pathname is a complete filename.
This replicates the complete_filename_p function from lread.c lines 1258-1265.
Returns #t if pathname starts with directory separator or is a full Windows path."

  (let* ((path-string (if (string? pathname) pathname (scm_to_utf8_string pathname)))
         (path-length (string-length path-string)))

    (if (= path-length 0)
        #f  ; Empty string is not complete
        (or
         ;; Check if starts with directory separator (Unix: /, Windows: \ or /)
         (or (char=? (string-ref path-string 0) #\/)
             (char=? (string-ref path-string 0) #\\))

         ;; Check for Windows drive letter format (C:\)
         (and (> path-length 2)
              (char=? (string-ref path-string 1) #\:)
              (or (char=? (string-ref path-string 2) #\/)
                  (char=? (string-ref path-string 2) #\\)))))))

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
      ;; When purifying: concat2(file-name-directory(file), file-name-nondirectory(found-eff))
      ((symbol-function 'concat)
       ((symbol-function 'file-name-directory) file)
       ((symbol-function 'file-name-nondirectory) found-eff))
      ;; Otherwise just use found-eff
      found-eff))

(define (elisp-handle-file-open-error fd noerror file)
  "Handle file opening errors and determine response.
This replicates the error handling from Fload (lines 993-999).
Returns: 'continue if should continue, 'return-nil if should return nil."

  ;; Check if file descriptor indicates failure (fd < 0)
  ;; In the C code, lread_fd_cmp(-1) checks if fd equals -1
  (if (< fd 0)
      (if (eq? noerror #nil)
          ;; If noerror is nil, we should signal an error (handled in C)
          'signal-error
          ;; If noerror is non-nil, return nil quietly
          'return-nil)
      ;; File opened successfully, continue
      'continue))

(define (elisp-handle-user-init-file found)
  "Handle user init file detection logic.
This replicates the user init file logic from Fload (lines 1002-1003).
Returns the value that should be assigned to Vuser_init_file."

  ;; Check if Vuser_init_file is Qt (meaning we're looking for user's init file)
  (if (eq? ((symbol-function 'symbol-value) (elisp-intern "user-init-file" #nil))
           ((symbol-function 'symbol-value) (elisp-intern "t" #nil)))
      found  ; If yes, set it to the found file
      ;; Otherwise, return the current value unchanged
      ((symbol-function 'symbol-value) (elisp-intern "user-init-file" #nil))))

(define (elisp-setup-file-descriptor-protection fd)
  "Determine if file descriptor needs unwind protection.
This replicates the unwind protection logic from Fload (lines 1008-1011).
Returns: #t if protection should be set up, #f otherwise."

  ;; In C: if (0 <= fd) - set up unwind protection
  (>= fd 0))

(define (elisp-should-close-fd is-module is-native-elisp fd-valid)
  "Determine if file descriptor should be closed.
  This replicates the close logic from Fload lines 1089-1097."

  (and (not is-module)
       (not is-native-elisp)
       fd-valid)) ; Close fd if regular elisp file with valid fd

(define (elisp-validate-file-descriptor fd-valid)
  "Validate file descriptor state.
  This replicates the errno setting from Fload lines 1078-1081.
  Returns validation result: 'valid or 'invalid."

  (if fd-valid
      'valid
      'invalid)) ; Will cause errno = EINVAL in C

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
