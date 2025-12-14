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

;;; ============================================================================
;;; SECTION 2: RELOAD INFRASTRUCTURE
;;; ============================================================================
;;;
;;; Functions for hot-reloading Elisp language components during development.
;;; This section is executed during prelude initialization.

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

;; Load consolidated text properties system as proper Guile module
;; This replaces the old 4-file split (intervals, emacs-string, text-properties, string-operations)
;; with a single unified module under (language elisp emacs text-properties) namespace
(primitive-load (string-append %prelude-directory "/elisp/runtime/text-properties.scm"))
(set-current-module (resolve-module '(language elisp runtime)))

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
