;;; * Guilemacs Bootstrap & Core Infrastructure
;;;   This file contains the core bootstrap code and infrastructure for Guilemacs.
;;;   Domain-specific runtime functions have been migrated to modular runtime files.
;;;
;;; ** Architecture
;;;   - Bootstrap & initialization code
;;;   - Runtime module loading infrastructure
;;;   - Elisp reader/parser functions (96 functions)
;;;   - File loading system (load, require, provide)
;;;   - Essential symbol management
;;;
;;; ** Modules
;;;   Runtime functionality is organized into focused modules:
;;;   Each runtime module manages its own symbol registrations via init functions.
;;; *** (language elisp types)
;;;   Type predicates & conversions
;;; *** (language/elisp numbers)
;;;   Arithmetic & math operations
;;; *** (language elisp strings)
;;;   String operations
;;; *** (language elisp sequences)
;;;   List & sequence operations
;;; *** (language elisp utils)
;;;   Property lists & utilities
;;; *** (language elisp loader)
;;;   Additional load support
;;; *** (language elisp reader)
;;;   Additional reader support
;;;

;; (force-output (current-error-port))
;; (format (current-error-port) "-- loading guile elisp prelude~%")
;; (format (current-error-port) "-- prelude path: ~s~%" %prelude-filename)
;; (force-output (current-error-port))

;; Load core runtime functions first - compute path relative to this file
;; Temporarily disabled to allow build to complete
;; (primitive-load (string-append (dirname (current-filename)) "/core-runtime.scm"))

;; (format (current-error-port) "-- current-module: ~s~%" (current-module))
;; (format (current-error-port) "-- prelude path: ~s~%" %prelude-filename)

;; Save prelude paths BEFORE switching modules, by keeping them in module guile-user
(define %saved-prelude-filename %prelude-filename)
(define %saved-prelude-directory (dirname %prelude-filename))

;; remove filename part of pathfile:
(let ((dir %saved-prelude-directory))
  (set! %load-path (cons (canonicalize-path (string-append dir "/../mod")) %load-path)))
;; (format (current-error-port) "-- %load-path: ~s~%" %load-path)

;; %prelude-filename is passed to us by try_load_guile_prelude
;; Note that we replace the guile's original runtime module here,
;; by reloading it with our local modifications
;(set! %load-path (cons "." %load-path))
;(set! %load-path (cons "./mod/" %load-path))


;; switch current-module to guile's original runtime module
;; Note that any changes to this module later on it scrapped,
;; because we do a module reload
(use-modules (emacs-elisp runtime))
;; (format (current-error-port) "-- loaded emacs-lisp runtime~%")
;; not sure this is needed anymore if we do pure modules
(set-current-module (resolve-module '(emacs-elisp runtime)))
;; (format (current-error-port) "-- switched module: ~s~%" (current-module))

(use-modules (rnrs bytevectors)) ; R6RS bytevector support (Guile standard)
(use-modules (language elisp emacs))
(use-modules (system foreign-library))

(use-modules ;(ice-9 auto-compile) ; enables the autocompile hook for loaders
             (ice-9 ftw) ; for stat etc.
             (system base compile) ; compile-file, compiled-file-name, etc.
             (system base language))

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


(set-current-module (resolve-module '(emacs-elisp runtime)))
;; Get saved values from guile-user module (where they were saved before switching)
(define %prelude-filename (module-ref (resolve-module '(guile-user)) '%saved-prelude-filename))
(define %prelude-directory (module-ref (resolve-module '(guile-user)) '%saved-prelude-directory))

(define (join a b)
  (if (or (string-null? a) (string-suffix? "/" a))
      (string-append a b)
      (string-append a "/" b)))

(define (compile-and-load-elisp path)
  ;; Compile PATH as Elisp, then load the resulting .go.
  ;; Skip compilation if .go is newer than source.
  (let* ((out (string-append path ".go"))
         (src-stat (stat path #f))
         (out-stat (stat out #f)))
    (when (or (not out-stat)
              (> (stat:mtime src-stat) (stat:mtime out-stat)))
      (compile-file path #:from 'elisp #:output-file out))
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

;; Files now in mod/emacs-elisp/ directory (one level up from prelude, then into mod)
(reload-local-elisp! (canonicalize-path (join %prelude-directory "../mod/emacs-elisp")))

(set-current-module (resolve-module '(emacs-elisp runtime)))

;; Initialize core Elisp variables BEFORE loading runtime modules
;; This breaks circular dependencies (e.g., featurep needs features)
(set-symbol-value! 'features '())

;; Load modular runtime components

;; Add prelude directory to load path so module files can be found
;; Module (language elisp types) maps to file language/elisp/types.scm
;; Files are in prelude/language/elisp/*.scm
(set! %load-path (cons %prelude-directory %load-path))

;; Load types module as proper Guile module
(use-modules (language elisp types))
;; Make all types functions available in (emacs-elisp runtime) namespace
(module-use! (current-module) (resolve-module '(language elisp types)))

;; Load numbers module as proper Guile module
(use-modules (language elisp numbers))
(module-use! (current-module) (resolve-module '(language elisp numbers)))

(use-modules (language elisp strings))
(use-modules (language elisp sequences))
(use-modules (language elisp utils))
(use-modules (language elisp loader))
(use-modules (language elisp reader))

;(let ((loader (lambda (file)
;                (primitive-load (join %prelude-directory file))
;                (set-current-module (resolve-module '(emacs-elisp runtime))))))
;  (loader "elisp/runtime/loader.scm")
;  (loader "elisp/runtime/reader.scm"))

(init-types-registrations)
(init-numbers-registrations)
(init-strings-registrations)
(init-sequences-registrations)
(init-utils-registrations)
(init-reader %prelude-directory)
(init-loader %prelude-directory)

;; Load pcase macro support (Phase 5 consolidation)
;; Replaces: pcase.scm
(use-modules (language elisp pcase))

;;; ============================================================================
;;; SECTION 8: ADDITIONAL DEFUN MIGRATIONS
;;; ============================================================================
;;;
;;; Additional function migrations from C to Guile from various source files.
;;; Includes functions from: lread.c, data.c, fns.c, floatfns.c
;;; NOTE: Some functions here may overlap with earlier sections.

;; Load lookup functions for C integration (Phase 4 consolidation)
;; Replaces: lookup-functions.scm
(primitive-load (join %prelude-directory "elisp/runtime/lookup-functions.scm"))

;; Load consolidated text properties system as proper Guile module
;; This replaces the old 4-file split (intervals, emacs-string, text-properties, string-operations)
;; with a single unified module under (language elisp emacs text-properties) namespace
(primitive-load (join %prelude-directory "elisp/runtime/text-properties.scm"))

;; Load consolidated UTF-8 string operations (Phase 2 consolidation)
;; Replaces: utf8-string-operations.scm (only file actually being loaded)
(set-current-module (resolve-module '(emacs-elisp runtime)))
(primitive-load (join %prelude-directory "language/elisp/utf8.scm"))

;; Load consolidated symbol and character operations (Phase 3 consolidation)
;; Replaces: symbol-operations.scm, character-navigation-minimal.scm
(set-current-module (resolve-module '(emacs-elisp runtime)))
(use-modules (language elisp symbol-operations))
(use-modules (language elisp character-predicates))

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
  ;; save-current-buffer is a MACRO defined in boot.el, not a function - don't register the Scheme version
  ;; (module-define! elisp-emacs-module 'save-current-buffer elisp-save-current-buffer)
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
