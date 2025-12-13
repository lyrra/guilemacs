;;; ============================================================================
;;; PRELUDE/LOAD.SCM - Guilemacs Bootstrap & Core Infrastructure
;;; ============================================================================
;;;
;;; This file contains the core bootstrap code and infrastructure for Guilemacs.
;;; Domain-specific runtime functions have been migrated to modular runtime files.
;;;
;;; ARCHITECTURE:
;;;   - Bootstrap & initialization code
;;;   - Runtime module loading infrastructure
;;;   - Elisp reader/parser functions (96 functions)
;;;   - File loading system (load, require, provide)
;;;   - Essential symbol management
;;;
;;; MODULAR RUNTIME:
;;;   Runtime functionality is organized into focused modules:
;;;   - elisp/runtime/types.scm     - Type predicates & conversions (41 functions)
;;;   - elisp/runtime/numbers.scm   - Arithmetic & math operations (32 functions)
;;;   - elisp/runtime/strings.scm   - String operations (27 functions)
;;;   - elisp/runtime/sequences.scm - List & sequence operations (34 functions)
;;;   - elisp/runtime/utils.scm     - Property lists & utilities (37 functions)
;;;   - elisp/runtime/loader.scm    - Additional load support
;;;   - elisp/runtime/reader.scm    - Additional reader support
;;;
;;;   Each runtime module manages its own symbol registrations via init functions.
;;;
;;; ============================================================================


;;; ============================================================================
;;; SECTION 1: MODULE SETUP & INITIALIZATION
;;; ============================================================================
;;;
;;; Sets up the runtime module, imports dependencies, and configures encoding.
;;; This section must come first as it establishes the execution environment.

;; (force-output (current-error-port))
;; (format (current-error-port) "-- loading guile elisp prelude~%")
;; (format (current-error-port) "-- prelude path: ~s~%" %prelude-filename)
;; (force-output (current-error-port))

;; Load core runtime functions first - compute path relative to this file
;; Temporarily disabled to allow build to complete
;; (primitive-load (string-append (dirname (current-filename)) "/core-runtime.scm"))

;; (format (current-error-port) "-- current-module: ~s~%" (current-module))
;; (force-output (current-error-port))

(set-current-module (resolve-module '(language elisp runtime)))

(use-modules (rnrs bytevectors)) ; FIX: move to (use-modules (scheme base))
(use-modules (language elisp emacs))
(use-modules (system foreign-library))

(use-modules ;(ice-9 auto-compile) ; enables the autocompile hook for loaders
             (ice-9 ftw) ; for stat etc.
             (system base compile) ; compile-file, compiled-file-name, etc.
             (system base language)
             ;; Don't load system elisp spec - use our custom one
             ;(language elisp spec)
             )

(use-modules (system base compile)       ; compile-file, compiled-file-name
             (system base language)      ; current-language parameter
             (ice-9 ftw))                ; file ops, optional

;; Map Emacs-specific encodings to Guile-compatible ones
;; Guile doesn't recognize "UTF-8-EMACS" but it's essentially UTF-8
(let ((original-set-port-encoding! set-port-encoding!))
  (set! set-port-encoding!
        (lambda (port encoding)
          "Wrapper for set-port-encoding! that maps Emacs encodings to Guile encodings"
          (let ((mapped-encoding
                 (cond
                  ((and (string? encoding) (string-ci=? encoding "UTF-8-EMACS")) "UTF-8")
                  ((and (string? encoding) (string-ci=? encoding "utf-8-emacs")) "UTF-8")
                  (else encoding))))
            (original-set-port-encoding! port mapped-encoding)))))


(set-current-module (resolve-module '(language elisp runtime)))
(define %prelude-directory (dirname %prelude-filename))

;; reload guile elisp language, to get modifications
(set! %load-path (cons "." %load-path))
(load "./elisp/runtime.scm")

;; Note: The join function is defined later in the reload infrastructure section
;; We'll add types module loading after that

;(format #t "------- reloading guile elisp runtime ----------~%")
;(format #t "scheme load-path: ~s~%" %load-path)
;(format #t "------- reloading guile elisp lexer ----------~%")
;(load "./elisp/lexer.scm")
;(format #t "------- reloading guile elisp parser ----------~%")
;(load "./elisp/parser.scm")
;(format #t "------- reloading guile elisp compile-tree-il ----------~%")
;(load "./elisp/compile-tree-il.scm")
;(format #t "------- reloading guile elisp boot.el ----------~%")
;(load "./elisp/boot.el")

;(format #t "------- reloading guile elisp spec ----------~%")
;(load "./elisp/spec.scm")

;;; End Section 1


;;; ============================================================================
;;; SECTION 2: RELOAD INFRASTRUCTURE
;;; ============================================================================
;;;
;;; Functions for hot-reloading Elisp language components during development.
;;; This section is executed during prelude initialization.

;----------------------------------------------------------------------------------
;; reload-elisp.scm
;; Reload language/elisp pieces in the right order and load boot.el as *Elisp*.
(define (join a b)
  (if (or (string-null? a) (string-suffix? "/" a))
      (string-append a b)
      (string-append a "/" b)))

(define (compile-and-load-elisp path)
  ;; Compile PATH as Elisp, then load the resulting .go.
  (let* ((out (string-append path ".go"))) ; avoid compiled-file-name
    (compile-file path #:from 'elisp #:output-file out)
    (load-compiled out)))

(define (reload-local-elisp! base-dir)
  "Reload local language/elisp Scheme pieces and boot.el from BASE-DIR.
   Order: runtime.scm → lexer.scm → parser.scm → compile-tree-il.scm → boot.el"
  (let* ((scheme-files '(; "runtime.scm" ; dont reload runtime it will redefine module
                         "lexer.scm"
                         "parser.scm"
                         "compile-tree-il.scm"))
         (old-load-path %load-path))
    (dynamic-wind
      (lambda () (set! %load-path (cons base-dir %load-path)))
      (lambda ()
        ;; 1) Reload Scheme-side modules in dependency order *as Scheme*.
        (for-each (lambda (f)
                    (let ((p (join base-dir f)))
                      (primitive-load p)))
                  scheme-files)
        ;; 2) Load boot.el *as Elisp*, either from source or via compiled .go.
        ; dont reload boot.el, move stuff into this file, or push upstream
        (compile-and-load-elisp (join base-dir "boot.el")))
      (lambda () (set! %load-path old-load-path)))))

(reload-local-elisp! (join %prelude-directory "elisp"))

(set-current-module (resolve-module '(language elisp runtime)))

;; Initialize core Elisp variables BEFORE loading runtime modules
;; This breaks circular dependencies (e.g., featurep needs features)
(set-symbol-value! 'features '())

;; Load modular runtime components
;; These submodules provide organized, maintainable runtime functionality
(primitive-load (join %prelude-directory "elisp/runtime/types.scm"))
(primitive-load (join %prelude-directory "elisp/runtime/numbers.scm"))
(primitive-load (join %prelude-directory "elisp/runtime/strings.scm"))
(primitive-load (join %prelude-directory "elisp/runtime/sequences.scm"))
(primitive-load (join %prelude-directory "elisp/runtime/utils.scm"))
(primitive-load (join %prelude-directory "elisp/runtime/loader.scm"))
(primitive-load (join %prelude-directory "elisp/runtime/reader.scm"))

;; Initialize symbol function registrations from runtime modules
;; This allows modules to manage their own registrations
(init-types-registrations)
(init-numbers-registrations)
(init-strings-registrations)
(init-sequences-registrations)
(init-utils-registrations)

(primitive-load (join %prelude-directory "pcase.scm"))

;;; End Section 2


;;; ============================================================================
;;; SECTION 3: ARITHMETIC & MATH OPERATIONS
;;; ============================================================================
;;;
;;; Migrated from C DEFUN arithmetic and mathematical functions.
;;; Includes: basic ops, floating point, predicates.
;;; NOTE: This section contains some duplicates that need cleanup.

(let-syntax
    ((frob (syntax-rules ()
             ((_ lisp-name fun-name)
              (begin
                (define fun-name (lambda args
                                   (apply lisp-name (map check-number-coerce-marker args))))
                (set-symbol-function! 'lisp-name fun-name))))))
  (frob min elisp-min)
  (frob max elisp-max)
  (frob + elisp-+)
  (frob - elisp--)
  (frob * elisp-*))





(let-syntax
    ((frob (syntax-rules ()
             ((_ lisp-name fun-name)
              (begin
                (define fun-name (lambda args
                                  (if (apply lisp-name (map check-number-coerce-marker args))
                                      #t #nil)))
                (set-symbol-function! 'lisp-name fun-name))))))
  (frob = elisp-=)
  (frob < elisp-<)
  (frob > elisp->)
  (frob <= elisp-<=)
  (frob >= elisp->=))

(let-syntax
    ((frob (syntax-rules ()
             ((_ el-name scm-op-arity1 scm-op-arity2)
              (set-symbol-function! 'el-name
                                    (lambda* (num #:optional div)
                                      (inexact->exact
                                       (if (not div)
                                           (scm-op-arity1 num)
                                           (scm-op-arity2 num div)))))))))
  (frob truncate truncate truncate-quotient)
  (frob ceiling  ceiling  ceiling-quotient)
  (frob floor    floor    floor-quotient)
  (frob round    round    round-quotient))

(let-syntax
    ((frob (syntax-rules ()
             ((_ el-name scm-op)
              (set-symbol-function! 'el-name
                                    (lambda (num)
                                      (unless (and (real? num) (not (exact? num)))
                                        ((symbol-function 'signal) 'wrong-type-argument num))
                                      (exact->inexact (scm-op num))))))))
  (frob ftruncate truncate)
  (frob fceiling ceiling)
  (frob ffloor floor)
  (frob fround round))


(define elisp-% (lambda (a b)
                  (remainder (check-number-coerce-marker a)
                             (check-number-coerce-marker b))))

;;; ============================================================================
;;; SECTION 4: STRING OPERATIONS
;;; ============================================================================
;;;
;;; String manipulation, comparison, and creation functions.
;;; Includes optimized C-string comparisons for C integration.

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

(define (elisp-check-file-handler file noerror nomessage nosuffix must-suffix)
  "Check for magic file name handler and call it if found.
  This replicates the handler check from Fload lines 973-977.
  Returns handler result or #f if no handler."

  (let ((handler ((symbol-function 'find-file-name-handler) file 'load)))
    (if handler
        ;; Call the handler with all arguments
        ((symbol-function 'funcall) handler 'load file noerror nomessage nosuffix must-suffix)
        #f))) ; No handler found

(define (elisp-compute-effective-filename found is-native-elisp)
  "Compute effective filename for loading.
  This replicates the found_eff computation from Fload lines 1040-1043."

  (if is-native-elisp
      ;; For native elisp, compute the effective name
      ((symbol-function 'compute-found-effective) found)
      ;; For regular files, use found as-is
      found))

(define (elisp-validate-file-descriptor fd-valid)
  "Validate file descriptor state.
  This replicates the errno setting from Fload lines 1078-1081.
  Returns validation result: 'valid or 'invalid."

  (if fd-valid
      'valid
      'invalid)) ; Will cause errno = EINVAL in C

(define (elisp-should-close-fd is-module is-native-elisp fd-valid)
  "Determine if file descriptor should be closed.
  This replicates the close logic from Fload lines 1089-1097."

  (and (not is-module)
       (not is-native-elisp)
       fd-valid)) ; Close fd if regular elisp file with valid fd

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

(define (elisp-prepare-load-bindings hist-file-name found)
  "Prepare all dynamic bindings for load operation.
  This replicates the specbind calls from Fload lines 1158-1161.
  Returns list of (symbol . value) pairs for C to bind."

  (list
   (cons 'load-file-name hist-file-name)
   (cons 'load-true-file-name found)
   (cons 'inhibit-file-name-operation #nil)
   (cons 'load-in-progress #t)))

(define (elisp-determine-load-action is-module)
  "Determine the loading action based on file type.
  This replicates the conditional logic from Fload lines 1173-1183.
  Returns: 'load-module or 'load-elisp."

  (if is-module
      'load-module
      'load-elisp))

(define (elisp-return-load-success)
  "Return success value for load operation completion.
  This replicates the final return Qt from Fload line 1235."
  #t) ; Return success

(define (elisp-load-with-match-data-protection file noerror nomessage nosuffix must-suffix)
  "Load file with match data protection.
  This replicates the save_match_data_load wrapper function."

  ;; Call the main load function - C will handle the match data protection
  ((symbol-function 'load) file noerror nomessage nosuffix must-suffix))

;; String function registrations migrated to prelude/elisp/runtime/strings.scm

;;; End Section 4

;;; ============================================================================
;;; SECTION 7: GOALS.ORG OPTIMIZATIONS
;;; ============================================================================
;;;
;;; Performance optimizations from goals.org:
;;; - Direct symbol comparison instead of string comparison
;;; - Native Guile case-insensitive operations
;;; - Symbol interning efficiency
;;; - Memory handling moved to Guile GC

;; Implementation of goals.org ideas
;; Goal: "Use direct symbol comparison instead of string comparison"

;;; ============================================================================
;;; SECTION 8: ADDITIONAL DEFUN MIGRATIONS
;;; ============================================================================
;;;
;;; Additional function migrations from C to Guile from various source files.
;;; Includes functions from: lread.c, data.c, fns.c, floatfns.c
;;; NOTE: Some functions here may overlap with earlier sections.

;; Load lookup functions for C integration
;; Use the prelude directory defined in the current module by C
(primitive-load (string-append %prelude-directory "/lookup-functions.scm"))

;; Load Phase 1 & 2 text properties wrapper infrastructure
;; These must be loaded in order: intervals -> emacs-string -> text-properties -> string-operations
;; Use save-module-excursion to preserve current module context
(let ((saved-module (current-module)))
  (primitive-load (string-append %prelude-directory "/intervals.scm"))
  (set-current-module saved-module)
  (primitive-load (string-append %prelude-directory "/emacs-string.scm"))
  (set-current-module saved-module)
  (primitive-load (string-append %prelude-directory "/text-properties.scm"))
  (set-current-module saved-module)
  (primitive-load (string-append %prelude-directory "/string-operations.scm"))
  (set-current-module saved-module))

;; Load new UTF-8 string operations and migration functions
(primitive-load (string-append %prelude-directory "/utf8-string-operations.scm"))
; FIX: disabled because of error, something with 'char=?'
;(primitive-load (string-append %prelude-directory "/string-comparison-migration.scm"))
(primitive-load (string-append %prelude-directory "/symbol-operations.scm"))

;; Load character navigation functions - Phase 2 UTF-8 migration improvements
;; Using minimal version that doesn't depend on buffer operations during bootstrap
(primitive-load (string-append %prelude-directory "/character-navigation-minimal.scm"))
;; Full version temporarily disabled due to buffer operation dependencies during bootstrap
;; TODO: Load full character-navigation.scm when buffer context is properly available
;; (primitive-load (string-append %prelude-directory "/character-navigation.scm"))


;; Export the functions to both global module and language elisp emacs module
;; so C code can find them from either location
(let ((elisp-emacs-module (resolve-module '(language elisp emacs) #f)))
  ;; Export to language elisp emacs module
  (module-define! elisp-emacs-module 'lookup-color-in-map lookup-color-in-map)
  (module-define! elisp-emacs-module 'lookup-font-style lookup-font-style)
  (module-define! elisp-emacs-module 'lookup-in-alist-ci lookup-in-alist-ci)
  (module-define! elisp-emacs-module 'lookup-in-alist lookup-in-alist)
  (module-define! elisp-emacs-module 'lookup-symbol-in-list lookup-symbol-in-list)
  (module-define! elisp-emacs-module 'parse-face-bool-attribute parse-face-bool-attribute)
  (module-define! elisp-emacs-module 'process-yesno-response process-yesno-response)
  (module-define! elisp-emacs-module 'filter-dbus-message filter-dbus-message)
  (module-define! elisp-emacs-module 'is-special-buffer-name? is-special-buffer-name?)
  (module-define! elisp-emacs-module 'parse-color-spec parse-color-spec)
  (module-define! elisp-emacs-module 'validate-color-name validate-color-name)
  (module-define! elisp-emacs-module 'string-contains-whitespace? string-contains-whitespace?)
  (module-define! elisp-emacs-module 'is-frame-name-fnn-format? is-frame-name-fnn-format?)
  (module-define! elisp-emacs-module 'validate-xlfd-font-name validate-xlfd-font-name)
  (module-define! elisp-emacs-module 'is-absolute-path? is-absolute-path?)
  (module-define! elisp-emacs-module 'has-directory-traversal? has-directory-traversal?)
  (module-define! elisp-emacs-module 'string-spaces-to-dashes string-spaces-to-dashes)
  (module-define! elisp-emacs-module 'string-trim-leading-whitespace string-trim-leading-whitespace)
  (module-define! elisp-emacs-module 'parse-number-string parse-number-string)
  (module-define! elisp-emacs-module 'validate-string-for-copying validate-string-for-copying)
  (module-define! elisp-emacs-module 'prepare-string-for-symbol prepare-string-for-symbol)

  ;; Export new SSDATA hoisting functions to elisp emacs module
  (module-define! elisp-emacs-module 'has-file-extension? has-file-extension?)
  (module-define! elisp-emacs-module 'extract-filename-from-path extract-filename-from-path)
  (module-define! elisp-emacs-module 'is-modifier-symbol? is-modifier-symbol?)
  (module-define! elisp-emacs-module 'validate-float-format-string validate-float-format-string)
  (module-define! elisp-emacs-module 'has-time-format-specifiers? has-time-format-specifiers?)
  (module-define! elisp-emacs-module 'parse-hex-color parse-hex-color)
  (module-define! elisp-emacs-module 'needs-filename-conversion? needs-filename-conversion?)
  (module-define! elisp-emacs-module 'is-utf8-filename? is-utf8-filename?)
  (module-define! elisp-emacs-module 'is-safe-for-c-string-copy? is-safe-for-c-string-copy?)
  (module-define! elisp-emacs-module 'looks-like-network-address? looks-like-network-address?)

  ;; Export path/filename operation functions to elisp emacs module
  (module-define! elisp-emacs-module 'is-absolute-path? is-absolute-path?)
  (module-define! elisp-emacs-module 'ends-with-directory-separator? ends-with-directory-separator?)
  (module-define! elisp-emacs-module 'normalize-path-separators normalize-path-separators)
  (module-define! elisp-emacs-module 'string-empty? string-empty?)
  (module-define! elisp-emacs-module 'has-directory-traversal? has-directory-traversal?)
  (module-define! elisp-emacs-module 'get-file-extension get-file-extension)
  (module-define! elisp-emacs-module 'path-starts-with? path-starts-with?)

  ;; Export simple string validation functions to elisp emacs module
  (module-define! elisp-emacs-module 'string-single-char? string-single-char?)
  (module-define! elisp-emacs-module 'string-starts-with-space? string-starts-with-space?)
  (module-define! elisp-emacs-module 'string-ascii-only? string-ascii-only?)
  (module-define! elisp-emacs-module 'valid-symbol-name? valid-symbol-name?)
  (module-define! elisp-emacs-module 'string-numeric? string-numeric?)
  (module-define! elisp-emacs-module 'string-needs-escaping? string-needs-escaping?)
  (module-define! elisp-emacs-module 'special-buffer-name? special-buffer-name?)
  (module-define! elisp-emacs-module 'string-equal-ignore-case? string-equal-ignore-case?)
  (module-define! elisp-emacs-module 'string-starts-with-char? string-starts-with-char?)
  (module-define! elisp-emacs-module 'string-ends-with-char? string-ends-with-char?)
  (module-define! elisp-emacs-module 'string-whitespace-only? string-whitespace-only?)
  (module-define! elisp-emacs-module 'valid-identifier? valid-identifier?)

  (module-define! elisp-emacs-module 'has-file-extension? has-file-extension?)

  ;; Export DEFUN function migrations to elisp emacs module
  (module-define! elisp-emacs-module 'integerp elisp-integerp)
  (module-define! elisp-emacs-module 'numberp elisp-numberp)
  (module-define! elisp-emacs-module 'null elisp-null)
  (module-define! elisp-emacs-module 'characterp elisp-characterp)
  (module-define! elisp-emacs-module 'symbolp elisp-symbolp)
  (module-define! elisp-emacs-module 'consp elisp-consp)
  (module-define! elisp-emacs-module 'atom elisp-atom)
  (module-define! elisp-emacs-module 'listp elisp-listp)
  (module-define! elisp-emacs-module 'nlistp elisp-nlistp)
  (module-define! elisp-emacs-module 'vectorp elisp-vectorp)
  (module-define! elisp-emacs-module 'sequencep elisp-sequencep)
  ;; (module-define! elisp-emacs-module 'markerp elisp-markerp)
  ;; (module-define! elisp-emacs-module 'keywordp elisp-keywordp)
  ;; (module-define! elisp-emacs-module 'identity elisp-identity)
  (module-define! elisp-emacs-module 'save-current-buffer elisp-save-current-buffer)
  (module-define! elisp-emacs-module 'with-current-buffer elisp-with-current-buffer)
  (module-define! elisp-emacs-module 'source-code-file? source-code-file?)
  (module-define! elisp-emacs-module 'image-file? image-file?)
  (module-define! elisp-emacs-module 'config-file? config-file?)
  (module-define! elisp-emacs-module 'extract-file-extension extract-file-extension)

  (module-define! elisp-emacs-module 'hex-color-string? hex-color-string?)
  (module-define! elisp-emacs-module 'rgb-color-string? rgb-color-string?)
  (module-define! elisp-emacs-module 'named-color? named-color?)
  (module-define! elisp-emacs-module 'valid-xlfd-font-name? valid-xlfd-font-name?)
  (module-define! elisp-emacs-module 'font-family-name? font-family-name?)

  (module-define! elisp-emacs-module 'url-string? url-string?)
  (module-define! elisp-emacs-module 'email-address? email-address?)
  (module-define! elisp-emacs-module 'ip-address? ip-address?)

  (module-define! elisp-emacs-module 'lookup-registry-to-script lookup-registry-to-script)

  (module-define! elisp-emacs-module 'parse-font-name-with-size parse-font-name-with-size)

  (module-define! elisp-emacs-module 'substring-no-properties-scheme substring-no-properties-scheme)

  ;; Export file path operation functions to both modules
  (module-define! elisp-emacs-module 'file-path-absolute-p file-path-absolute-p)
  (module-define! elisp-emacs-module 'file-path-directory file-path-directory)
  (module-define! elisp-emacs-module 'file-path-nondirectory file-path-nondirectory)
  (module-define! elisp-emacs-module 'file-path-safe-p file-path-safe-p)

  ;; Export string concatenation functions to both modules
  (module-define! elisp-emacs-module 'string-concat-2 string-concat-2)
  (module-define! elisp-emacs-module 'string-concat-3 string-concat-3)
  (module-define! elisp-emacs-module 'string-concat-multi string-concat-multi)

  ;; Export integer parsing functions to both modules
  (module-define! elisp-emacs-module 'parse-integer-string parse-integer-string)
  (module-define! elisp-emacs-module 'read-integer-guile read-integer-guile)
  (module-define! elisp-emacs-module 'parse-emacs-number parse-emacs-number))

;; when elisp reads keyword symbols, support common-lisp keywords
(read-set! keywords 'prefix)

;;; ============================================================================
;;; SECTION 9: READER & PARSER FUNCTIONS
;;; ============================================================================
;;;
;;; Elisp reader implementation - parses lists, vectors, literals, etc.
;;; Migrated from lread.c to enable better extensibility.
;;; This is a large section with 50+ parse functions.

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
C has already consumed the opening quote, so we read the complete string.
Returns: the parsed string"
  ;; Use Guile's built-in string reader
  (read port))

(define (elisp-parse-string-literal-from-port-enhanced port)
  "Parse a string literal from PORT with enhanced quote handling.
This version handles the case where C has consumed the opening quote.
Returns: the parsed string with proper type validation in Scheme"
  ;; C puts back the quote, so we can use normal read
  (let ((result (read port)))
    (cond
      ((eof-object? result)
       (error "Unexpected EOF while reading string"))
      ((string? result) result)
      (else
       (error "String parser returned non-string")))))

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

      ;; Unsupported syntax - consistent error messages
      ((char=? ch #\s)
       (error "Hash-table/record syntax (#s) not supported"))
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

(define (elisp-parse-colon-prefixed-symbol port)
  "Parse a colon-prefixed symbol like :keyword from PORT.
Assumes the colon has already been consumed and we're reading the rest."
  (let ((name ":"))  ; Start with colon
    (let loop ()
      (let ((ch (peek-char port)))
        (cond
          ;; EOF or terminator character - done reading symbol
          ((or (eof-object? ch)
               (char<=? ch #\space)
               (char=? ch #\")
               (char=? ch #\')
               (char=? ch #\;)
               (char=? ch #\()
               (char=? ch #\))
               (char=? ch #\[)
               (char=? ch #\])
               (char=? ch #\#)
               (char=? ch #\?)
               (char=? ch #\`)
               (char=? ch #\,)
               (char=? ch #\.))
           ;; Done - create the symbol
           (string->symbol name))

          ;; Regular symbol character - add to name and continue
          (else
           (read-char port) ; consume the character
           (set! name (string-append name (string ch)))
           (loop)))))))

(define (elisp-parse-symbol-from-port port)
  "Parse symbol or number from PORT with comprehensive Elisp conversion.
Called from C fread0() when alphabetic character is encountered.
Handles special symbol identity mapping, keyword conversion, and uninterned symbols.
Returns the parsed object with proper Elisp semantics."
  ;; Let Guile's read function handle the complete parsing
  (let ((result (read port)))
    (cond
      ;; Handle EOF
      ((eof-object? result)
       (error "Unexpected EOF while reading symbol"))

      ;; Handle symbols with special identity mapping
      ((symbol? result)
       (let ((sym-str (symbol->string result)))
         (cond
           ;; Reader macro symbols - map to canonical Elisp symbols
           ((or (string=? sym-str "`") (string=? sym-str "\\`"))
            ;; Backquote symbol - use existing Qbackquote
            ((symbol-function 'intern) "`" #nil))
           ((or (string=? sym-str ",") (string=? sym-str "\\,"))
            ;; Unquote symbol - use existing Qcomma
            ((symbol-function 'intern) "," #nil))
           ((or (string=? sym-str ",@") (string=? sym-str "\\,@"))
            ;; Unquote-splicing symbol - use existing Qcomma_at
            ((symbol-function 'intern) ",@" #nil))

           ;; Special Elisp symbols - use canonical values
           ((string=? sym-str "nil")
            ;; Return canonical Elisp nil
            (elisp-nil))
           ((string=? sym-str "t")
            ;; Return canonical Elisp t
            (elisp-t))
           ((string=? sym-str "and")
            ;; Map to canonical interned symbol
            ((symbol-function 'intern) "and" #nil))
           ((string=? sym-str ":")
            ;; Map colon to canonical interned symbol
            ((symbol-function 'intern) ":" #nil))

           ;; Regular symbols - intern normally
           (else
            ((symbol-function 'intern) sym-str #nil)))))

      ;; Handle Guile keywords - convert to Elisp colon symbols
      ((keyword? result)
       (let* ((keyword-symbol (keyword->symbol result))
              (base-name (symbol->string keyword-symbol))
              (colon-name (string-append ":" base-name)))
         ;; Create Elisp symbol with colon prefix
         (let ((elisp-symbol ((symbol-function 'intern) colon-name #nil)))
           ;; Make it self-evaluating (keywords evaluate to themselves)
           ((symbol-function 'set) elisp-symbol elisp-symbol)
           elisp-symbol)))

      ;; Numbers and other types pass through directly
      (else result))))

(define (elisp-parse-number-from-port port)
  "Parse number from PORT using Guile's read with proper error handling.
Called from C fread0() when numeric character is encountered.
Returns the parsed number or symbol with proper Elisp semantics."
  ;; Let Guile's read function handle the complete parsing
  (let ((result (read port)))
    (cond
      ;; Handle EOF
      ((eof-object? result)
       (error "Unexpected EOF while reading number"))

      ;; Numbers pass through directly - Guile's parsing is authoritative
      ((number? result)
       result)

      ;; If not a number, it might be a symbol that looks numeric (like +foo, -bar, .symbol)
      ;; Use the symbol parsing logic
      ((symbol? result)
       (let ((sym-str (symbol->string result)))
         ((symbol-function 'intern) sym-str #nil)))

      ;; Other types pass through (shouldn't happen in practice)
      (else result))))

(define (elisp-intern-and-make-keyword str)
  "Intern STR as Elisp symbol and make it self-evaluating if it's a keyword."
  (let ((elisp-symbol ((symbol-function 'intern) str #nil)))
    ;; If it's a keyword (starts with :), make it self-evaluating
    (if (and (> (string-length str) 0) (char=? (string-ref str 0) #\:))
        ((symbol-function 'set) elisp-symbol elisp-symbol))
    elisp-symbol))

(define (elisp-parse-colon-prefixed-symbol-and-intern port)
  "Parse a colon-prefixed symbol from PORT and return proper Elisp symbol.
Assumes the colon has already been consumed."
  (let ((name ":"))  ; Start with colon
    (let loop ()
      (let ((ch (peek-char port)))
        (cond
          ;; EOF or terminator character - done reading symbol
          ((or (eof-object? ch)
               (char<=? ch #\space)
               (char=? ch #\")
               (char=? ch #\')
               (char=? ch #\;)
               (char=? ch #\()
               (char=? ch #\))
               (char=? ch #\[)
               (char=? ch #\])
               (char=? ch #\#)
               (char=? ch #\?)
               (char=? ch #\`)
               (char=? ch #\,)
               (char=? ch #\.))
           ;; Done - intern as Elisp symbol with keyword self-evaluation
           (elisp-intern-and-make-keyword name))

          ;; Regular symbol character - add to name and continue
          (else
           (read-char port) ; consume the character
           (set! name (string-append name (string ch)))
           (loop)))))))


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

(define (elisp-setup-default-lexical-binding)
  "Set up default dynamic binding for load context.
This replicates the lexical binding setup from Fload (lines 1046-1050).
All loads are by default dynamic, unless the file itself specifies otherwise."

  ;; Bind lexical-binding to nil (dynamic binding by default)
  ;; This will be handled by specbind in the C wrapper since it needs proper cleanup
  'setup-for-c-specbind)

(define (elisp-call-load-source-file-function load-source-file-function found hist-file-name noerror nomessage force-load-messages)
  "Call the load-source-file-function with properly converted arguments.
This replicates the call4 logic from Fload (lines 1065-1067)."

  ;; Convert arguments to match the C call4 pattern
  (let ((error-arg (if (eq? noerror #nil) #nil #t))
        (message-arg (if (or (eq? nomessage #nil) force-load-messages) #nil #t)))

    ;; Call the function with 4 arguments
    ((symbol-function 'funcall) load-source-file-function found hist-file-name error-arg message-arg)))

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

(define (elisp-prepare-module-loading found)
  "Prepare for module loading by initializing load history.
This replicates the module loading preparation from Fload (lines 1176-1178)."

  ;; Call loadhist-initialize for the found file
  ;; This corresponds to the C code: loadhist_initialize (found);
  ((symbol-function 'loadhist-initialize) found))

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

(define (elisp-setup-file-descriptor-protection fd)
  "Determine if file descriptor needs unwind protection.
This replicates the unwind protection logic from Fload (lines 1008-1011).
Returns: #t if protection should be set up, #f otherwise."

  ;; In C: if (0 <= fd) - set up unwind protection
  (>= fd 0))

(define (elisp-prepare-openp-call path-result)
  "Prepare parameters for openp function call.
This replicates the openp call preparation from Fload (lines 985-991).
Returns: (processed-file . suffixes) pair for openp call."

  ;; Extract the components that were computed by elisp-process-load-file-path
  ;; path_result is already a (file . suffixes) pair from scheme
  path-result)

(define (elisp-handle-loads-in-progress found loads-in-progress)
  "Prepare loads-in-progress list update.
This extends the recursive load handling from Fload (lines 1027-1029).
Returns: the new value for loads-in-progress list."

  ;; The C code does: Vloads_in_progress = Fcons (found, Vloads_in_progress);
  ;; We return the new cons cell for C to assign
  ((symbol-function 'cons) found loads-in-progress))

;; COMPOUND FUNCTIONS - Consolidate multiple operations to reduce C-Guile marshalling

(define (elisp-validate-and-check-handler file noerror nomessage nosuffix must-suffix)
  "Compound function: Validate file and check for magic file name handlers.
This consolidates elisp-validate-load-file and elisp-check-file-handler.
Returns: handler result if handler found, #f if should continue with normal loading."

  ;; First, validate the file
  (elisp-validate-load-file file)

  ;; Then check for magic file name handlers
  (elisp-check-file-handler file noerror nomessage nosuffix must-suffix))

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

(define (fresh-go? go src)
  (and go
       (file-exists? go)
       (>= (stat:mtime (stat go)) (stat:mtime (stat src)))))

(define (load-elisp file)
  (let* ((src (%search-load-path file)) ; find foo.el on %load-path
         (go  (compiled-file-name src)) ; cache path for .go
         (el  (lookup-language 'elisp)))
    (unless src
      (error "Not found on %load-path" file))
    (if (fresh-go? go src)
        (load-compiled go)
        (begin
          (compile-file src
                        #:from el ; 'elisp
                        ;#:to 'value ; warmbyte , FIX-GUILE: cant combine with output-file
                        #:output-file go)
          (load-compiled go)))))

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


;; Enhanced version that handles full Fload parameters
(define (load-elisp-full found-file noerror nomessage nosuffix must-suffix)
  "Load elisp file with compilation, handling full Fload parameter set"
  (catch #t
    (lambda ()
      (let* ((src found-file)
             (go (string-append src ".go")) ; FIX: compiled-file-name returns #f ?!
             ;; Load our custom elisp language to override system elisp
             (el (lookup-language 'elisp)))
        (if (fresh-go? go src)
            (load-compiled go)
            (begin
              (compile-file src
                            #:from el
                            #:output-file go)
              (load-compiled go)))
        #t)) ; return t on success
    (lambda (key . args)
      (if noerror
          #f ; return nil on error if noerror is true
          (apply throw key args))))) ; re-throw error otherwise

; FIX: kludge, move to some init function
(let ((str (canonicalize-path (string-concatenate (list %prelude-directory "/..")))))
  (set! %load-path (append (list (string-concatenate (list str "/lisp"))
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
                                 (string-concatenate (list str "/lisp/eshell")))
                           %load-path)))

(set! %load-extensions (cons ".el" %load-extensions))

;; Bridge function that reuses existing Fload Scheme migrations
(define (fload-bridge file noerror nomessage nosuffix must-suffix)
  "Bridge function that handles full Fload protocol using Guile elisp compilation"
  (catch #t
    (lambda ()
      (format (current-error-port) "loading ~a~%" file)
      ;; File validation and handler check (reuse existing)
      (let ((handler-result (elisp-validate-and-check-handler file noerror nomessage nosuffix must-suffix)))
        (when handler-result
          (throw 'early-return handler-result)))

      ;; File path processing and suffix determination (reuse existing)
      (let* ((path-result (elisp-process-load-file-path file nosuffix must-suffix)
                          ;(cons file '(".el" ".elc"))
                         )
             (processed-file (car path-result))
             (suffixes (cdr path-result)))
        ;; Find file using openp equivalent, including current directory
        (let ((found (or
                         ; FIX: %search-load-path is underspecified, does it search for compiled equivalent and if so, how is given suffix handled?
                         (%search-load-path processed-file)
                         ;processed-file
                         ;; Also try current directory if not found in load-path
                         (and (file-exists? processed-file) processed-file)
                         ;; Try with .el suffix in current directory
                         (and (file-exists? (string-append processed-file ".el"))
                              (string-append processed-file ".el")))))
          (unless found
            (if noerror
                (throw 'early-return #f)
                (error "Cannot open load file" file)))

          ;; Step 4: Setup load environment (reuse existing)
          (let ((setup-env-func (resolve-ref "language elisp runtime"
                                            "elisp-setup-load-environment")))
            (when setup-env-func
              (setup-env-func found '() file #f #t))) ; simplified params

          ;; Step 5: Use enhanced elisp compilation instead of C reading
          (load-elisp-full found noerror nomessage nosuffix must-suffix))))

    (lambda (key . args)
      (cond
        ((eq? key 'early-return) (car args))
        (noerror #f)
        (else (apply throw key args))))))

;; Helper to safely resolve scheme functions
(define (resolve-ref module-name symbol-name)
  (catch #t
    (lambda ()
      (let ((mod (resolve-module (string->symbol module-name))))
        (and mod (module-ref mod (string->symbol symbol-name)))))
    (lambda (key . args) #f)))

(set-symbol-function! 'emacs-load fload-bridge)

;;; End Section 10


;;; ============================================================================
;;; SECTION 11: DEBUG & DEVELOPMENT TOOLS
;;; ============================================================================
;;;
;;; Utilities for debugging and development - not part of core runtime.
;;; Includes: symbol generation, debug flags, eval-scheme for testing.

;; Define intern-gensym first - creates interned unique symbols
(define %intern-gensym 0)
(define (intern-gensym prefix)
  (set! %intern-gensym (+ 1 %intern-gensym))
  (string->symbol (string-concatenate (list prefix "_" (number->string %intern-gensym)))))

;; Make make-symbol create interned symbols (not uninterned) to avoid Guile serialization errors
;; Uninterned symbols cannot be saved to .go files
(define (make-symbol name)
  (intern-gensym name))
(set-symbol-function! 'make-symbol make-symbol)

(set-symbol-function! 'intern-gensym intern-gensym)

(define %debug-print-flag 0)
(define (set-debug-print-flag! val)
  (set! %debug-print-flag val))

;(define (get-debug-print-flag)
;  %debug-print-flag)
(set-symbol-function! 'set-debug-print-flag! set-debug-print-flag!)

(set-symbol-function! 'get-debug-print-flag
                      (lambda ()
                        %debug-print-flag))

;;; End Section 11


;;; ============================================================================
;;; END OF PRELUDE/LOAD.SCM
;;; ============================================================================

;; (format (current-error-port) "-- done loading guile elisp prelude~%")
;; (force-output (current-error-port))
