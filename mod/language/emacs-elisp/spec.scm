;; Copyright (C) Free Software Foundation, Inc.
;; SPDX-License-Identifier: GPL-3.0-or-later

;; M60 imp-3: the language REGISTRATION lives here, because Guile
;; `lookup-language' resolves `(language NAME spec)' and then reads the
;; binding NAME in that module (system/base/language.scm:62 ... :66).
;; The module holds the language object only.  The boot compile stays in
;; (emacs-elisp spec), so this module has no cycle with it.
(define-module (language emacs-elisp spec)
  #:use-module (emacs-elisp parser)
  #:use-module (emacs-elisp compile-tree-il)
  #:use-module (system base language)
  #:export (emacs-elisp))

(define-language emacs-elisp
  #:title     "Modern Emacs Lisp"
  #:reader    (lambda (port env) (read-elisp port))
  ;;#:joiner (lambda (exps env) (cons 'progn exps))
  #:printer   write
  #:compilers `((tree-il . ,compile-tree-il)))
