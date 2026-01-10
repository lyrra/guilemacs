;; Copyright (C) Free Software Foundation, Inc.
;; SPDX-License-Identifier: GPL-3.0-or-later

(define-module (emacs-elisp runtime function-slot)
  #:use-module ((emacs-elisp compile-tree-il)
                #:select
                ((compile-progn . progn)
                 (compile-eval-when-compile . eval-when-compile)
                 (compile-if . if)
                 (compile-defconst . defconst)
                 (compile-defvar . defvar)
                 (compile-setq . setq)
                 (compile-let . let)
                 (compile-flet . flet)
                 (compile-labels . labels)
                 (compile-let* . let*)
                 (compile-guile-ref . guile-ref)
                 (compile-guile-private-ref . guile-private-ref)
                 (compile-guile-primitive . guile-primitive)
                 (compile-function . function)
                 (compile-defun . defun)
                 (compile-defmacro . defmacro)
                 (#{compile-`}# . #{`}#)
                 (compile-quote . quote)
                 (compile-%funcall . %funcall)
                 (compile-%set-lexical-binding-mode
                  . %set-lexical-binding-mode)))
  #:duplicates (last)
  ;; special operators
  #:re-export (progn
               eval-when-compile
               if
               defconst
               defvar
               setq
               let
               flet
               labels
               let*
               guile-ref
               guile-private-ref
               guile-primitive
               function
               defun
               defmacro
               #{`}#
               quote
               %funcall
               %set-lexical-binding-mode)
  #:declarative? #f
  #:pure)
