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
;;; *** (emacs types)
;;;   Type predicates & conversions
;;; *** (language/elisp numbers)
;;;   Arithmetic & math operations
;;; *** (emacs strings)
;;;   String operations
;;; *** (emacs sequences)
;;;   List & sequence operations
;;; *** (emacs utils)
;;;   Property lists & utilities
;;; *** (emacs loader)
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

;-------------------
; monkey patch guile
;-------------------
;; Replace lookup-language to find our emacs-elisp language module
;; instead of looking in (language NAME spec) which is Guile's default
(let ((lang-module (resolve-module '(system base language)))
      (compile-module (resolve-module '(system base compile)))
      (original-lookup (module-ref (resolve-module '(system base language)) 'lookup-language))
      (original-default-env (module-ref (resolve-module '(system base language)) 'default-environment)))
  (let ((patched-lookup
         (lambda (name)
           ;; For emacs-elisp, look in (emacs-elisp spec) not (language emacs-elisp spec)
           (if (equal? 'lisp name)
               (error "bad language: elisp"))
           (if (eq? name 'emacs-elisp)
               (let ((m (resolve-module '(emacs-elisp spec))))
                 (if (module-bound? m 'emacs-elisp)
                     (module-ref m 'emacs-elisp)
                     (error "emacs-elisp language not found in module")))
               ;; For other languages, use original lookup
               (original-lookup name)))))
    ;; Patch lookup-language in both modules
    (module-set! lang-module 'lookup-language patched-lookup)
    (module-set! compile-module 'lookup-language patched-lookup)
    ;; Also patch default-environment to use our patched lookup
    (let ((patched-default-env
           (lambda (lang)
             (let ((language-make-default-environment
                    (module-ref lang-module 'language-make-default-environment)))
               ((language-make-default-environment
                 (if ((module-ref lang-module 'language?) lang)
                     lang
                     (patched-lookup lang))))))))
      (module-set! lang-module 'default-environment patched-default-env)
      (module-set! compile-module 'default-environment patched-default-env))))
;===================

(use-modules (rnrs bytevectors) ; R6RS bytevector support (Guile standard)
             (system foreign-library)
             (system base compile) ; compile-file, compiled-file-name, etc.
             (system base language)
             ;(ice-9 auto-compile) ; enables the autocompile hook for loaders
             (ice-9 ftw)) ; for stat etc.

(use-modules (emacs-elisp runtime)
             (emacs-elisp compile-tree-il)
             (language elisp emacs))

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

(set-current-module (resolve-module '(emacs-elisp runtime)))

;; Initialize core Elisp variables BEFORE loading runtime modules
;; This breaks circular dependencies (e.g., featurep needs features)
(set-symbol-value! 'features '())

;; Load modular runtime components

;; Add prelude directory to load path so module files can be found
(set! %load-path (cons %prelude-directory %load-path))

;; Load types module as proper Guile module
(use-modules (emacs types))
;; Make all types functions available in (emacs-elisp runtime) namespace
(module-use! (current-module) (resolve-module '(emacs types)))

;; Load numbers module as proper Guile module
(use-modules (numbers))
(use-modules (emacs strings))
(use-modules (emacs sequences))
(use-modules (emacs utils))
(use-modules (emacs loader))
(use-modules (emacs reader))
(use-modules (emacs lookup-functions))

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
(init-lookup-functions)

(use-modules (emacs pcase))

;;; ============================================================================
;;; SECTION 8: ADDITIONAL DEFUN MIGRATIONS
;;; ============================================================================
;;;
;;; Additional function migrations from C to Guile from various source files.
;;; Includes functions from: lread.c, data.c, fns.c, floatfns.c
;;; NOTE: Some functions here may overlap with earlier sections.

(set-current-module (resolve-module '(emacs-elisp runtime)))
(use-modules (emacs text-properties))
(use-modules (emacs utf8))


(set-current-module (resolve-module '(emacs-elisp runtime)))
(use-modules (emacs symbol-operations))
(use-modules (emacs character-predicates))

;; Export the functions to both global module and language elisp emacs module
;; so C code can find them from either location
(let ((elisp-emacs-module (resolve-module '(language elisp emacs) #f)))
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
  )
;; when elisp reads keyword symbols, support common-lisp keywords
(read-set! keywords 'prefix)
