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
             (ice-9 ftw)  ; for stat etc.
             (emacs-elisp runtime)
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

;; Load core emacs functionallity
(use-modules (emacs boot))
(use-modules (emacs list))
(use-modules (emacs types))
(use-modules (emacs numbers))
(use-modules (emacs debug))
(use-modules (emacs strings))
(use-modules (emacs sequences))
(use-modules (emacs utils))
(use-modules (emacs loader))
(use-modules (emacs reader))
(use-modules (emacs lookup-functions))
(use-modules (emacs pcase))
(use-modules (emacs text-properties))
(use-modules (emacs utf8))
(use-modules (emacs symbol-operations))
(use-modules (emacs character-predicates))

(format (current-error-port) ";; initializing emacs modules~%")
(init-boot-registrations)
(init-list-registrations)
(init-types-registrations)
(init-numbers-registrations)
(init-debug-registrations)
(init-strings-registrations)
(init-sequences-registrations)
(init-utils-registrations)
(init-reader %prelude-directory)
(init-loader %prelude-directory)
(init-lookup-functions)

(set-symbol-value! 'features '())
(read-set! keywords 'prefix)

(format (current-error-port) ";; load.scm done~%")
