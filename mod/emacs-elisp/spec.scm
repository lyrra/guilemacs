;; Copyright (C) Free Software Foundation, Inc.
;; SPDX-License-Identifier: GPL-3.0-or-later

(define-module (emacs-elisp spec)
  #:use-module (emacs-elisp compile-tree-il)
  #:use-module (emacs-elisp parser)
  #:use-module (emacs-elisp falias)  ; Pre-load before boot.el compilation
  #:use-module (system base language)
  #:use-module (system base compile)
  #:use-module (system base target)
  #:use-module (system vm vm)
  #:export (emacs-elisp))

(save-module-excursion
 (lambda ()
   (define-module (elisp-symbols) #:pure #:filename #f)
   (define-module (elisp-functions) #:pure #:filename #f)
   (define-module (elisp-plists) #:pure #:filename #f)))

(define-language emacs-elisp
  #:title     "Modern Emacs Lisp"
  #:reader    (lambda (port env) (read-elisp port))
  ;;#:joiner (lambda (exps env) (cons 'progn exps))
  #:printer   write
  #:compilers `((tree-il . ,compile-tree-il)))

(set-default-vm-engine! 'debug)
(set-vm-engine! 'debug)

;; Compile and load the Elisp boot code for the native host
;; architecture.  We must specifically ask for native compilation here,
;; because this module might be loaded in a dynamic environment where
;; cross-compilation has been requested using 'with-target'.  For
;; example, this happens when cross-compiling Guile itself.
(with-native-target
  (lambda ()
    (compile-and-load (%search-load-path "emacs-elisp/boot.el")
                      #:from 'emacs-elisp)))
